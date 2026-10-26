import V185TrunkScan22Chunk356

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3185344 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 2, 4]
def baseStart_3185344 : Nat := 118140960795 + 3185344 * 2 ^ 59
def prefixEnd_3185344 : Nat := 4983230072969 + 3 ^ 40 * 3185344 * 2
def baseEnd_3185344 : Nat := 1090408347943527040433917

theorem tailTrace_3185344 : CollatzResearch.WordTrace tailWord_3185344 prefixEnd_3185344 1090408347943527040433917 := by
  unfold tailWord_3185344
  simp only [CollatzResearch.WordTrace]
  refine ⟨58089520086025088144593543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77452693448033450859458057 58089520086025088144593543)
  ·
    refine ⟨87134280129037632216890315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58089520086025088144593543 87134280129037632216890315)
    ·
      refine ⟨130701420193556448325335473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87134280129037632216890315 130701420193556448325335473)
      ·
        refine ⟨98026065145167336244001605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130701420193556448325335473 98026065145167336244001605)
        ·
          refine ⟨18379887214718875545750301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98026065145167336244001605 18379887214718875545750301)
          ·
            refine ⟨6892457705519578329656363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18379887214718875545750301 6892457705519578329656363)
            ·
              refine ⟨10338686558279367494484545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6892457705519578329656363 10338686558279367494484545)
              ·
                refine ⟨7754014918709525620863409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10338686558279367494484545 7754014918709525620863409)
                ·
                  refine ⟨5815511189032144215647557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7754014918709525620863409 5815511189032144215647557)
                  ·
                    refine ⟨1090408347943527040433917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5815511189032144215647557 1090408347943527040433917)
                    ·
                      rfl

theorem cell22_3185344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_3185344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185344 prefixEnd_3185344 := by exact prefixLift 3185344
  have htrace : WordTrace (prefixWord ++ tailWord_3185344) baseStart_3185344 baseEnd_3185344 := by
    simpa [prefixWord, tailWord_3185344, baseEnd_3185344] using wordTrace_append hprefix tailTrace_3185344
  have hstable : (prefixWord ++ tailWord_3185344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185344).length < 2 ^ (prefixWord ++ tailWord_3185344).sum := by decide
  have hdescent : baseEnd_3185344 < baseStart_3185344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185348 : List Nat := [2, 3, 3, 1, 1, 3, 3, 2, 4]
def baseStart_3185348 : Nat := 118140960795 + 3185348 * 2 ^ 59
def prefixEnd_3185348 : Nat := 4983230072969 + 3 ^ 40 * 3185348 * 2
def baseEnd_3185348 : Nat := 363469905741757454444635

theorem tailTrace_3185348 : CollatzResearch.WordTrace tailWord_3185348 prefixEnd_3185348 363469905741757454444635 := by
  unfold tailWord_3185348
  simp only [CollatzResearch.WordTrace]
  refine ⟨58089593032017842486166349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77452790709357123314888465 58089593032017842486166349)
  ·
    refine ⟨21783597387006690932312381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58089593032017842486166349 21783597387006690932312381)
    ·
      refine ⟨8168849020127509099617143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21783597387006690932312381 8168849020127509099617143)
      ·
        refine ⟨12253273530191263649425715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8168849020127509099617143 12253273530191263649425715)
        ·
          refine ⟨18379910295286895474138573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12253273530191263649425715 18379910295286895474138573)
          ·
            refine ⟨6892466360732585802801965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18379910295286895474138573 6892466360732585802801965)
            ·
              refine ⟨2584674885274719676050737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6892466360732585802801965 2584674885274719676050737)
              ·
                refine ⟨1938506163956039757038053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2584674885274719676050737 1938506163956039757038053)
                ·
                  refine ⟨363469905741757454444635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1938506163956039757038053 363469905741757454444635)
                  ·
                    rfl

theorem cell22_3185348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_3185348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185348 prefixEnd_3185348 := by exact prefixLift 3185348
  have htrace : WordTrace (prefixWord ++ tailWord_3185348) baseStart_3185348 baseEnd_3185348 := by
    simpa [prefixWord, tailWord_3185348, baseEnd_3185348] using wordTrace_append hprefix tailTrace_3185348
  have hstable : (prefixWord ++ tailWord_3185348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185348).length < 2 ^ (prefixWord ++ tailWord_3185348).sum := by decide
  have hdescent : baseEnd_3185348 < baseStart_3185348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185397 : List Nat := [1, 3, 6, 1, 1, 1, 2, 2, 2, 3]
def baseStart_3185397 : Nat := 118140960795 + 3185397 * 2 ^ 59
def prefixEnd_3185397 : Nat := 4983230072969 + 3 ^ 40 * 3185397 * 2
def baseEnd_3185397 : Nat := 1090426490926652568858755

theorem tailTrace_3185397 : CollatzResearch.WordTrace tailWord_3185397 prefixEnd_3185397 1090426490926652568858755 := by
  unfold tailWord_3185397
  simp only [CollatzResearch.WordTrace]
  refine ⟨116180973240858166340866445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77453982160572110893910963 116180973240858166340866445)
  ·
    refine ⟨43567864965321812377824917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116180973240858166340866445 43567864965321812377824917)
    ·
      refine ⟨2042243670249459955210543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43567864965321812377824917 2042243670249459955210543)
      ·
        refine ⟨3063365505374189932815815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2042243670249459955210543 3063365505374189932815815)
        ·
          refine ⟨4595048258061284899223723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3063365505374189932815815 4595048258061284899223723)
          ·
            refine ⟨6892572387091927348835585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595048258061284899223723 6892572387091927348835585)
            ·
              refine ⟨5169429290318945511626689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6892572387091927348835585 5169429290318945511626689)
              ·
                refine ⟨3877071967739209133720017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5169429290318945511626689 3877071967739209133720017)
                ·
                  refine ⟨2907803975804406850290013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3877071967739209133720017 2907803975804406850290013)
                  ·
                    refine ⟨1090426490926652568858755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2907803975804406850290013 1090426490926652568858755)
                    ·
                      rfl

theorem cell22_3185397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_3185397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185397 prefixEnd_3185397 := by exact prefixLift 3185397
  have htrace : WordTrace (prefixWord ++ tailWord_3185397) baseStart_3185397 baseEnd_3185397 := by
    simpa [prefixWord, tailWord_3185397, baseEnd_3185397] using wordTrace_append hprefix tailTrace_3185397
  have hstable : (prefixWord ++ tailWord_3185397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185397).length < 2 ^ (prefixWord ++ tailWord_3185397).sum := by decide
  have hdescent : baseEnd_3185397 < baseStart_3185397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185404 : List Nat := [2, 2, 2, 1, 3, 2, 1, 4, 5]
def baseStart_3185404 : Nat := 118140960795 + 3185404 * 2 ^ 59
def prefixEnd_3185404 : Nat := 4983230072969 + 3 ^ 40 * 3185404 * 2
def baseEnd_3185404 : Nat := 363476295723235627977911

theorem tailTrace_3185404 : CollatzResearch.WordTrace tailWord_3185404 prefixEnd_3185404 363476295723235627977911 := by
  unfold tailWord_3185404
  simp only [CollatzResearch.WordTrace]
  refine ⟨58090614275916403268185633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77454152367888537690914177 58090614275916403268185633)
  ·
    refine ⟨43567960706937302451139225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58090614275916403268185633 43567960706937302451139225)
    ·
      refine ⟨32675970530202976838354419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43567960706937302451139225 32675970530202976838354419)
      ·
        refine ⟨49013955795304465257531629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32675970530202976838354419 49013955795304465257531629)
        ·
          refine ⟨18380233423239174471574361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49013955795304465257531629 18380233423239174471574361)
          ·
            refine ⟨13785175067429380853680771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18380233423239174471574361 13785175067429380853680771)
            ·
              refine ⟨20677762601144071280521157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13785175067429380853680771 20677762601144071280521157)
              ·
                refine ⟨3877080487714513365097717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20677762601144071280521157 3877080487714513365097717)
                ·
                  refine ⟨363476295723235627977911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3877080487714513365097717 363476295723235627977911)
                  ·
                    rfl

theorem cell22_3185404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_3185404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185404 prefixEnd_3185404 := by exact prefixLift 3185404
  have htrace : WordTrace (prefixWord ++ tailWord_3185404) baseStart_3185404 baseEnd_3185404 := by
    simpa [prefixWord, tailWord_3185404, baseEnd_3185404] using wordTrace_append hprefix tailTrace_3185404
  have hstable : (prefixWord ++ tailWord_3185404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185404).length < 2 ^ (prefixWord ++ tailWord_3185404).sum := by decide
  have hdescent : baseEnd_3185404 < baseStart_3185404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185434 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_3185434 : Nat := 118140960795 + 3185434 * 2 ^ 59
def prefixEnd_3185434 : Nat := 4983230072969 + 3 ^ 40 * 3185434 * 2
def baseEnd_3185434 : Nat := 1090439156782796805683641

theorem tailTrace_3185434 : CollatzResearch.WordTrace tailWord_3185434 prefixEnd_3185434 1090439156782796805683641 := by
  unfold tailWord_3185434
  simp only [CollatzResearch.WordTrace]
  refine ⟨29045580685431030414990839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77454881827816081106642237 29045580685431030414990839)
  ·
    refine ⟨43568371028146545622486259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29045580685431030414990839 43568371028146545622486259)
    ·
      refine ⟨65352556542219818433729389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43568371028146545622486259 65352556542219818433729389)
      ·
        refine ⟨24507208703332431912648521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65352556542219818433729389 24507208703332431912648521)
        ·
          refine ⟨18380406527499323934486391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24507208703332431912648521 18380406527499323934486391)
          ·
            refine ⟨27570609791248985901729587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18380406527499323934486391 27570609791248985901729587)
            ·
              refine ⟨41355914686873478852594381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27570609791248985901729587 41355914686873478852594381)
              ·
                refine ⟨15508468007577554569722893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41355914686873478852594381 15508468007577554569722893)
                ·
                  refine ⟨5815675502841582963646085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15508468007577554569722893 5815675502841582963646085)
                  ·
                    refine ⟨1090439156782796805683641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5815675502841582963646085 1090439156782796805683641)
                    ·
                      rfl

theorem cell22_3185434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_3185434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185434 prefixEnd_3185434 := by exact prefixLift 3185434
  have htrace : WordTrace (prefixWord ++ tailWord_3185434) baseStart_3185434 baseEnd_3185434 := by
    simpa [prefixWord, tailWord_3185434, baseEnd_3185434] using wordTrace_append hprefix tailTrace_3185434
  have hstable : (prefixWord ++ tailWord_3185434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185434).length < 2 ^ (prefixWord ++ tailWord_3185434).sum := by decide
  have hdescent : baseEnd_3185434 < baseStart_3185434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185466 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 6]
def baseStart_3185466 : Nat := 118140960795 + 3185466 * 2 ^ 59
def prefixEnd_3185466 : Nat := 4983230072969 + 3 ^ 40 * 3185466 * 2
def baseEnd_3185466 : Nat := 363483370345586462961181

theorem tailTrace_3185466 : CollatzResearch.WordTrace tailWord_3185466 prefixEnd_3185466 363483370345586462961181 := by
  unfold tailWord_3185466
  simp only [CollatzResearch.WordTrace]
  refine ⟨29045872469402047781282063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77455659918405460750085501 29045872469402047781282063)
  ·
    refine ⟨43568808704103071671923095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29045872469402047781282063 43568808704103071671923095)
    ·
      refine ⟨65353213056154607507884643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43568808704103071671923095 65353213056154607507884643)
      ·
        refine ⟨98029819584231911261826965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65353213056154607507884643 98029819584231911261826965)
        ·
          refine ⟨4595147793010870840398139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98029819584231911261826965 4595147793010870840398139)
          ·
            refine ⟨6892721689516306260597209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595147793010870840398139 6892721689516306260597209)
            ·
              refine ⟨5169541267137229695447907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6892721689516306260597209 5169541267137229695447907)
              ·
                refine ⟨7754311900705844543171861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5169541267137229695447907 7754311900705844543171861)
                ·
                  refine ⟨363483370345586462961181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7754311900705844543171861 363483370345586462961181)
                  ·
                    rfl

theorem cell22_3185466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_3185466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185466 prefixEnd_3185466 := by exact prefixLift 3185466
  have htrace : WordTrace (prefixWord ++ tailWord_3185466) baseStart_3185466 baseEnd_3185466 := by
    simpa [prefixWord, tailWord_3185466, baseEnd_3185466] using wordTrace_append hprefix tailTrace_3185466
  have hstable : (prefixWord ++ tailWord_3185466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185466).length < 2 ^ (prefixWord ++ tailWord_3185466).sum := by decide
  have hdescent : baseEnd_3185466 < baseStart_3185466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185481 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 1, 5]
def baseStart_3185481 : Nat := 118140960795 + 3185481 * 2 ^ 59
def prefixEnd_3185481 : Nat := 4983230072969 + 3 ^ 40 * 3185481 * 2
def baseEnd_3185481 : Nat := 1090455245843304349758497

theorem tailTrace_3185481 : CollatzResearch.WordTrace tailWord_3185481 prefixEnd_3185481 1090455245843304349758497 := by
  unfold tailWord_3185481
  simp only [CollatzResearch.WordTrace]
  refine ⟨116184036972553848686924297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77456024648369232457949531 116184036972553848686924297)
  ·
    refine ⟨87138027729415386515193223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116184036972553848686924297 87138027729415386515193223)
    ·
      refine ⟨130707041594123079772789835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87138027729415386515193223 130707041594123079772789835)
      ·
        refine ⟨196060562391184619659184753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130707041594123079772789835 196060562391184619659184753)
        ·
          refine ⟨147045421793388464744388565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196060562391184619659184753 147045421793388464744388565)
          ·
            refine ⟨3446377073282542142446607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 147045421793388464744388565 3446377073282542142446607)
            ·
              refine ⟨5169565609923813213669911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446377073282542142446607 5169565609923813213669911)
              ·
                refine ⟨7754348414885719820504867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5169565609923813213669911 7754348414885719820504867)
                ·
                  refine ⟨11631522622328579730757301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7754348414885719820504867 11631522622328579730757301)
                  ·
                    refine ⟨1090455245843304349758497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11631522622328579730757301 1090455245843304349758497)
                    ·
                      rfl

theorem cell22_3185481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 5].length) (baseStart_3185481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185481 prefixEnd_3185481 := by exact prefixLift 3185481
  have htrace : WordTrace (prefixWord ++ tailWord_3185481) baseStart_3185481 baseEnd_3185481 := by
    simpa [prefixWord, tailWord_3185481, baseEnd_3185481] using wordTrace_append hprefix tailTrace_3185481
  have hstable : (prefixWord ++ tailWord_3185481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185481).length < 2 ^ (prefixWord ++ tailWord_3185481).sum := by decide
  have hdescent : baseEnd_3185481 < baseStart_3185481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185485 : List Nat := [1, 6, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_3185485 : Nat := 118140960795 + 3185485 * 2 ^ 59
def prefixEnd_3185485 : Nat := 4983230072969 + 3 ^ 40 * 3185485 * 2
def baseEnd_3185485 : Nat := 1090456615125049672658485

theorem tailTrace_3185485 : CollatzResearch.WordTrace tailWord_3185485 prefixEnd_3185485 1090456615125049672658485 := by
  unfold tailWord_3185485
  simp only [CollatzResearch.WordTrace]
  refine ⟨116184182864539357370069909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77456121909692904913379939 116184182864539357370069909)
  ·
    refine ⟨5446133571775282376722027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116184182864539357370069909 5446133571775282376722027)
    ·
      refine ⟨8169200357662923565083041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5446133571775282376722027 8169200357662923565083041)
      ·
        refine ⟨6126900268247192673812281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8169200357662923565083041 6126900268247192673812281)
        ·
          refine ⟨4595175201185394505359211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6126900268247192673812281 4595175201185394505359211)
          ·
            refine ⟨6892762801778091758038817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595175201185394505359211 6892762801778091758038817)
            ·
              refine ⟨5169572101333568818529113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6892762801778091758038817 5169572101333568818529113)
              ·
                refine ⟨3877179076000176613896835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5169572101333568818529113 3877179076000176613896835)
                ·
                  refine ⟨5815768614000264920845253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877179076000176613896835 5815768614000264920845253)
                  ·
                    refine ⟨1090456615125049672658485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5815768614000264920845253 1090456615125049672658485)
                    ·
                      rfl

theorem cell22_3185485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_3185485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185485 prefixEnd_3185485 := by exact prefixLift 3185485
  have htrace : WordTrace (prefixWord ++ tailWord_3185485) baseStart_3185485 baseEnd_3185485 := by
    simpa [prefixWord, tailWord_3185485, baseEnd_3185485] using wordTrace_append hprefix tailTrace_3185485
  have hstable : (prefixWord ++ tailWord_3185485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185485).length < 2 ^ (prefixWord ++ tailWord_3185485).sum := by decide
  have hdescent : baseEnd_3185485 < baseStart_3185485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185500 : List Nat := [2, 2, 4, 2, 1, 3, 1, 3, 4]
def baseStart_3185500 : Nat := 118140960795 + 3185500 * 2 ^ 59
def prefixEnd_3185500 : Nat := 4983230072969 + 3 ^ 40 * 3185500 * 2
def baseEnd_3185500 : Nat := 363487249977198211177813

theorem tailTrace_3185500 : CollatzResearch.WordTrace tailWord_3185500 prefixEnd_3185500 363487249977198211177813 := by
  unfold tailWord_3185500
  simp only [CollatzResearch.WordTrace]
  refine ⟨58092364979742507465932977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77456486639656676621243969 58092364979742507465932977)
  ·
    refine ⟨43569273734806880599449733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58092364979742507465932977 43569273734806880599449733)
    ·
      refine ⟨8169238825276290112396825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43569273734806880599449733 8169238825276290112396825)
      ·
        refine ⟨6126929118957217584297619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8169238825276290112396825 6126929118957217584297619)
        ·
          refine ⟨9190393678435826376446429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6126929118957217584297619 9190393678435826376446429)
          ·
            refine ⟨3446397629413434891167411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9190393678435826376446429 3446397629413434891167411)
            ·
              refine ⟨5169596444120152336751117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446397629413434891167411 5169596444120152336751117)
              ·
                refine ⟨1938598666545057126281669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5169596444120152336751117 1938598666545057126281669)
                ·
                  refine ⟨363487249977198211177813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1938598666545057126281669 363487249977198211177813)
                  ·
                    rfl

theorem cell22_3185500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_3185500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185500 prefixEnd_3185500 := by exact prefixLift 3185500
  have htrace : WordTrace (prefixWord ++ tailWord_3185500) baseStart_3185500 baseEnd_3185500 := by
    simpa [prefixWord, tailWord_3185500, baseEnd_3185500] using wordTrace_append hprefix tailTrace_3185500
  have hstable : (prefixWord ++ tailWord_3185500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185500).length < 2 ^ (prefixWord ++ tailWord_3185500).sum := by decide
  have hdescent : baseEnd_3185500 < baseStart_3185500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185588 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3185588 : Nat := 118140960795 + 3185588 * 2 ^ 59
def prefixEnd_3185588 : Nat := 4983230072969 + 3 ^ 40 * 3185588 * 2
def baseEnd_3185588 : Nat := 1090491874129991737333169

theorem tailTrace_3185588 : CollatzResearch.WordTrace tailWord_3185588 prefixEnd_3185588 1090491874129991737333169 := by
  unfold tailWord_3185588
  simp only [CollatzResearch.WordTrace]
  refine ⟨58093969791583102980534709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77458626388777470640712945 58093969791583102980534709)
  ·
    refine ⟨5446309667960915904425129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58093969791583102980534709 5446309667960915904425129)
    ·
      refine ⟨4084732250970686928318847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5446309667960915904425129 4084732250970686928318847)
      ·
        refine ⟨6127098376456030392478271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4084732250970686928318847 6127098376456030392478271)
        ·
          refine ⟨9190647564684045588717407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6127098376456030392478271 9190647564684045588717407)
          ·
            refine ⟨13785971347026068383076111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9190647564684045588717407 13785971347026068383076111)
            ·
              refine ⟨20678957020539102574614167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13785971347026068383076111 20678957020539102574614167)
              ·
                refine ⟨31018435530808653861921251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20678957020539102574614167 31018435530808653861921251)
                ·
                  refine ⟨46527653296212980792881877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31018435530808653861921251 46527653296212980792881877)
                  ·
                    refine ⟨1090491874129991737333169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46527653296212980792881877 1090491874129991737333169)
                    ·
                      rfl

theorem cell22_3185588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3185588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185588 prefixEnd_3185588 := by exact prefixLift 3185588
  have htrace : WordTrace (prefixWord ++ tailWord_3185588) baseStart_3185588 baseEnd_3185588 := by
    simpa [prefixWord, tailWord_3185588, baseEnd_3185588] using wordTrace_append hprefix tailTrace_3185588
  have hstable : (prefixWord ++ tailWord_3185588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185588).length < 2 ^ (prefixWord ++ tailWord_3185588).sum := by decide
  have hdescent : baseEnd_3185588 < baseStart_3185588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185616 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 4, 3]
def baseStart_3185616 : Nat := 118140960795 + 3185616 * 2 ^ 59
def prefixEnd_3185616 : Nat := 4983230072969 + 3 ^ 40 * 3185616 * 2
def baseEnd_3185616 : Nat := 1090501459102208997633083

theorem tailTrace_3185616 : CollatzResearch.WordTrace tailWord_3185616 prefixEnd_3185616 1090501459102208997633083 := by
  unfold tailWord_3185616
  simp only [CollatzResearch.WordTrace]
  refine ⟨58094480413532383371544351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77459307218043177828725801 58094480413532383371544351)
  ·
    refine ⟨87141720620298575057316527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58094480413532383371544351 87141720620298575057316527)
    ·
      refine ⟨130712580930447862585974791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87141720620298575057316527 130712580930447862585974791)
      ·
        refine ⟨196068871395671793878962187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130712580930447862585974791 196068871395671793878962187)
        ·
          refine ⟨294103307093507690818443281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196068871395671793878962187 294103307093507690818443281)
          ·
            refine ⟨220577480320130768113832461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294103307093507690818443281 220577480320130768113832461)
            ·
              refine ⟨82716555120049038042687173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220577480320130768113832461 82716555120049038042687173)
              ·
                refine ⟨15509354085009194633003845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82716555120049038042687173 15509354085009194633003845)
                ·
                  refine ⟨2908003890939223993688221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15509354085009194633003845 2908003890939223993688221)
                  ·
                    refine ⟨1090501459102208997633083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2908003890939223993688221 1090501459102208997633083)
                    ·
                      rfl

theorem cell22_3185616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 4, 3].length) (baseStart_3185616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185616 prefixEnd_3185616 := by exact prefixLift 3185616
  have htrace : WordTrace (prefixWord ++ tailWord_3185616) baseStart_3185616 baseEnd_3185616 := by
    simpa [prefixWord, tailWord_3185616, baseEnd_3185616] using wordTrace_append hprefix tailTrace_3185616
  have hstable : (prefixWord ++ tailWord_3185616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185616).length < 2 ^ (prefixWord ++ tailWord_3185616).sum := by decide
  have hdescent : baseEnd_3185616 < baseStart_3185616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185620 : List Nat := [2, 4, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_3185620 : Nat := 118140960795 + 3185620 * 2 ^ 59
def prefixEnd_3185620 : Nat := 4983230072969 + 3 ^ 40 * 3185620 * 2
def baseEnd_3185620 : Nat := 1090502828383954320533071

theorem tailTrace_3185620 : CollatzResearch.WordTrace tailWord_3185620 prefixEnd_3185620 1090502828383954320533071 := by
  unfold tailWord_3185620
  simp only [CollatzResearch.WordTrace]
  refine ⟨58094553359525137713117157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77459404479366850284156209 58094553359525137713117157)
  ·
    refine ⟨10892728754910963321209467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58094553359525137713117157 10892728754910963321209467)
    ·
      refine ⟨16339093132366444981814201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10892728754910963321209467 16339093132366444981814201)
      ·
        refine ⟨12254319849274833736360651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16339093132366444981814201 12254319849274833736360651)
        ·
          refine ⟨18381479773912250604540977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12254319849274833736360651 18381479773912250604540977)
          ·
            refine ⟨13786109830434187953405733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18381479773912250604540977 13786109830434187953405733)
            ·
              refine ⟨2584895593206410241263575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13786109830434187953405733 2584895593206410241263575)
              ·
                refine ⟨3877343389809615361895363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584895593206410241263575 3877343389809615361895363)
                ·
                  refine ⟨5816015084714423042843045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877343389809615361895363 5816015084714423042843045)
                  ·
                    refine ⟨1090502828383954320533071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5816015084714423042843045 1090502828383954320533071)
                    ·
                      rfl

theorem cell22_3185620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_3185620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185620 prefixEnd_3185620 := by exact prefixLift 3185620
  have htrace : WordTrace (prefixWord ++ tailWord_3185620) baseStart_3185620 baseEnd_3185620 := by
    simpa [prefixWord, tailWord_3185620, baseEnd_3185620] using wordTrace_append hprefix tailTrace_3185620
  have hstable : (prefixWord ++ tailWord_3185620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185620).length < 2 ^ (prefixWord ++ tailWord_3185620).sum := by decide
  have hdescent : baseEnd_3185620 < baseStart_3185620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185695 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 3, 3]
def baseStart_3185695 : Nat := 118140960795 + 3185695 * 2 ^ 59
def prefixEnd_3185695 : Nat := 4983230072969 + 3 ^ 40 * 3185695 * 2
def baseEnd_3185695 : Nat := 1090528502416679124907841

theorem tailTrace_3185695 : CollatzResearch.WordTrace tailWord_3185695 prefixEnd_3185695 1090528502416679124907841 := by
  unfold tailWord_3185695
  simp only [CollatzResearch.WordTrace]
  refine ⟨116191842193778563235214539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77461228129185708823476359 116191842193778563235214539)
  ·
    refine ⟨174287763290667844852821809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116191842193778563235214539 174287763290667844852821809)
    ·
      refine ⟨130715822468000883639616357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174287763290667844852821809 130715822468000883639616357)
      ·
        refine ⟨24509216712750165682428067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130715822468000883639616357 24509216712750165682428067)
        ·
          refine ⟨36763825069125248523642101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24509216712750165682428067 36763825069125248523642101)
          ·
            refine ⟨3446608600230492049091447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36763825069125248523642101 3446608600230492049091447)
            ·
              refine ⟨5169912900345738073637171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446608600230492049091447 5169912900345738073637171)
              ·
                refine ⟨7754869350518607110455757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5169912900345738073637171 7754869350518607110455757)
                ·
                  refine ⟨2908076006444477666420909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7754869350518607110455757 2908076006444477666420909)
                  ·
                    refine ⟨1090528502416679124907841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2908076006444477666420909 1090528502416679124907841)
                    ·
                      rfl

theorem cell22_3185695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 3].length) (baseStart_3185695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185695 prefixEnd_3185695 := by exact prefixLift 3185695
  have htrace : WordTrace (prefixWord ++ tailWord_3185695) baseStart_3185695 baseEnd_3185695 := by
    simpa [prefixWord, tailWord_3185695, baseEnd_3185695] using wordTrace_append hprefix tailTrace_3185695
  have hstable : (prefixWord ++ tailWord_3185695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185695).length < 2 ^ (prefixWord ++ tailWord_3185695).sum := by decide
  have hdescent : baseEnd_3185695 < baseStart_3185695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185738 : List Nat := [3, 1, 2, 1, 1, 2, 2, 5, 1, 4]
def baseStart_3185738 : Nat := 118140960795 + 3185738 * 2 ^ 59
def prefixEnd_3185738 : Nat := 4983230072969 + 3 ^ 40 * 3185738 * 2
def baseEnd_3185738 : Nat := 1090543222195441346082709

theorem tailTrace_3185738 : CollatzResearch.WordTrace tailWord_3185738 prefixEnd_3185738 1090543222195441346082709 := by
  unfold tailWord_3185738
  simp only [CollatzResearch.WordTrace]
  refine ⟨29048352633155695394757467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77462273688415187719353245 29048352633155695394757467)
  ·
    refine ⟨43572528949733543092136201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29048352633155695394757467 43572528949733543092136201)
    ·
      refine ⟨32679396712300157319102151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43572528949733543092136201 32679396712300157319102151)
      ·
        refine ⟨49019095068450235978653227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32679396712300157319102151 49019095068450235978653227)
        ·
          refine ⟨73528642602675353967979841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49019095068450235978653227 73528642602675353967979841)
          ·
            refine ⟨55146481952006515475984881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73528642602675353967979841 55146481952006515475984881)
            ·
              refine ⟨41359861464004886606988661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55146481952006515475984881 41359861464004886606988661)
              ·
                refine ⟨3877487012250458119405187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41359861464004886606988661 3877487012250458119405187)
                ·
                  refine ⟨5816230518375687179107781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877487012250458119405187 5816230518375687179107781)
                  ·
                    refine ⟨1090543222195441346082709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5816230518375687179107781 1090543222195441346082709)
                    ·
                      rfl

theorem cell22_3185738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_3185738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185738 prefixEnd_3185738 := by exact prefixLift 3185738
  have htrace : WordTrace (prefixWord ++ tailWord_3185738) baseStart_3185738 baseEnd_3185738 := by
    simpa [prefixWord, tailWord_3185738, baseEnd_3185738] using wordTrace_append hprefix tailTrace_3185738
  have hstable : (prefixWord ++ tailWord_3185738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185738).length < 2 ^ (prefixWord ++ tailWord_3185738).sum := by decide
  have hdescent : baseEnd_3185738 < baseStart_3185738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185751 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 5, 5]
def baseStart_3185751 : Nat := 118140960795 + 3185751 * 2 ^ 59
def prefixEnd_3185751 : Nat := 4983230072969 + 3 ^ 40 * 3185751 * 2
def baseEnd_3185751 : Nat := 1090547672361113645507669

theorem tailTrace_3185751 : CollatzResearch.WordTrace tailWord_3185751 prefixEnd_3185751 1090547672361113645507669 := by
  unfold tailWord_3185751
  simp only [CollatzResearch.WordTrace]
  refine ⟨116193884681575684799253107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77462589787717123199502071 116193884681575684799253107)
  ·
    refine ⟨174290827022363527198879661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116193884681575684799253107 174290827022363527198879661)
    ·
      refine ⟨65359060133386322699579873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174290827022363527198879661 65359060133386322699579873)
      ·
        refine ⟨49019295100039742024684905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65359060133386322699579873 49019295100039742024684905)
        ·
          refine ⟨36764471325029806518513679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49019295100039742024684905 36764471325029806518513679)
          ·
            refine ⟨55146706987544709777770519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36764471325029806518513679 55146706987544709777770519)
            ·
              refine ⟨82720060481317064666655779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55146706987544709777770519 82720060481317064666655779)
              ·
                refine ⟨124080090721975596999983669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82720060481317064666655779 124080090721975596999983669)
                ·
                  refine ⟨11632508505185212218748469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124080090721975596999983669 11632508505185212218748469)
                  ·
                    refine ⟨1090547672361113645507669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11632508505185212218748469 1090547672361113645507669)
                    ·
                      rfl

theorem cell22_3185751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_3185751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185751 prefixEnd_3185751 := by exact prefixLift 3185751
  have htrace : WordTrace (prefixWord ++ tailWord_3185751) baseStart_3185751 baseEnd_3185751 := by
    simpa [prefixWord, tailWord_3185751, baseEnd_3185751] using wordTrace_append hprefix tailTrace_3185751
  have hstable : (prefixWord ++ tailWord_3185751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185751).length < 2 ^ (prefixWord ++ tailWord_3185751).sum := by decide
  have hdescent : baseEnd_3185751 < baseStart_3185751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185811 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 1, 8]
def baseStart_3185811 : Nat := 118140960795 + 3185811 * 2 ^ 59
def prefixEnd_3185811 : Nat := 4983230072969 + 3 ^ 40 * 3185811 * 2
def baseEnd_3185811 : Nat := 1090568211587293489007485

theorem tailTrace_3185811 : CollatzResearch.WordTrace tailWord_3185811 prefixEnd_3185811 1090568211587293489007485 := by
  unfold tailWord_3185811
  simp only [CollatzResearch.WordTrace]
  refine ⟨116196073061358315046437287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77464048707572210030958191 116196073061358315046437287)
  ·
    refine ⟨174294109592037472569655931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116196073061358315046437287 174294109592037472569655931)
    ·
      refine ⟨261441164388056208854483897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174294109592037472569655931 261441164388056208854483897)
      ·
        refine ⟨196080873291042156640862923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261441164388056208854483897 196080873291042156640862923)
        ·
          refine ⟨294121309936563234961294385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196080873291042156640862923 294121309936563234961294385)
          ·
            refine ⟨220590982452422426220970789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294121309936563234961294385 220590982452422426220970789)
            ·
              refine ⟨41360809209829204916432023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220590982452422426220970789 41360809209829204916432023)
              ·
                refine ⟨62041213814743807374648035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41360809209829204916432023 62041213814743807374648035)
                ·
                  refine ⟨93061820722115711061972053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62041213814743807374648035 93061820722115711061972053)
                  ·
                    refine ⟨1090568211587293489007485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93061820722115711061972053 1090568211587293489007485)
                    ·
                      rfl

theorem cell22_3185811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_3185811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185811 prefixEnd_3185811 := by exact prefixLift 3185811
  have htrace : WordTrace (prefixWord ++ tailWord_3185811) baseStart_3185811 baseEnd_3185811 := by
    simpa [prefixWord, tailWord_3185811, baseEnd_3185811] using wordTrace_append hprefix tailTrace_3185811
  have hstable : (prefixWord ++ tailWord_3185811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185811).length < 2 ^ (prefixWord ++ tailWord_3185811).sum := by decide
  have hdescent : baseEnd_3185811 < baseStart_3185811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185873 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 3, 4]
def baseStart_3185873 : Nat := 118140960795 + 3185873 * 2 ^ 59
def prefixEnd_3185873 : Nat := 4983230072969 + 3 ^ 40 * 3185873 * 2
def baseEnd_3185873 : Nat := 1090589435454345993957295

theorem tailTrace_3185873 : CollatzResearch.WordTrace tailWord_3185873 prefixEnd_3185873 1090589435454345993957295 := by
  unfold tailWord_3185873
  simp only [CollatzResearch.WordTrace]
  refine ⟨116198334387133699635194273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77465556258089133090129515 116198334387133699635194273)
  ·
    refine ⟨87148750790350274726395705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116198334387133699635194273 87148750790350274726395705)
    ·
      refine ⟨65361563092762706044796779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87148750790350274726395705 65361563092762706044796779)
      ·
        refine ⟨98042344639144059067195169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65361563092762706044796779 98042344639144059067195169)
        ·
          refine ⟨73531758479358044300396377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98042344639144059067195169 73531758479358044300396377)
          ·
            refine ⟨55148818859518533225297283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73531758479358044300396377 55148818859518533225297283)
            ·
              refine ⟨82723228289277799837945925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55148818859518533225297283 82723228289277799837945925)
              ·
                refine ⟨15510605304239587469614861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82723228289277799837945925 15510605304239587469614861)
                ·
                  refine ⟨5816476989089845301105573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15510605304239587469614861 5816476989089845301105573)
                  ·
                    refine ⟨1090589435454345993957295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5816476989089845301105573 1090589435454345993957295)
                    ·
                      rfl

theorem cell22_3185873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_3185873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185873 prefixEnd_3185873 := by exact prefixLift 3185873
  have htrace : WordTrace (prefixWord ++ tailWord_3185873) baseStart_3185873 baseEnd_3185873 := by
    simpa [prefixWord, tailWord_3185873, baseEnd_3185873] using wordTrace_append hprefix tailTrace_3185873
  have hstable : (prefixWord ++ tailWord_3185873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185873).length < 2 ^ (prefixWord ++ tailWord_3185873).sum := by decide
  have hdescent : baseEnd_3185873 < baseStart_3185873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185877 : List Nat := [1, 3, 2, 4, 1, 1, 4, 1, 5]
def baseStart_3185877 : Nat := 118140960795 + 3185877 * 2 ^ 59
def prefixEnd_3185877 : Nat := 4983230072969 + 3 ^ 40 * 3185877 * 2
def baseEnd_3185877 : Nat := 363530268245363772285761

theorem tailTrace_3185877 : CollatzResearch.WordTrace tailWord_3185877 prefixEnd_3185877 363530268245363772285761 := by
  unfold tailWord_3185877
  simp only [CollatzResearch.WordTrace]
  refine ⟨116198480279119208318339885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77465653519412805545559923 116198480279119208318339885)
  ·
    refine ⟨43574430104669703119377457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116198480279119208318339885 43574430104669703119377457)
    ·
      refine ⟨32680822578502277339533093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43574430104669703119377457 32680822578502277339533093)
      ·
        refine ⟨6127654233469177001162455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32680822578502277339533093 6127654233469177001162455)
        ·
          refine ⟨9191481350203765501743683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6127654233469177001162455 9191481350203765501743683)
          ·
            refine ⟨13787222025305648252615525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9191481350203765501743683 13787222025305648252615525)
            ·
              refine ⟨2585104129744809047365411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13787222025305648252615525 2585104129744809047365411)
              ·
                refine ⟨3877656194617213571048117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585104129744809047365411 3877656194617213571048117)
                ·
                  refine ⟨363530268245363772285761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3877656194617213571048117 363530268245363772285761)
                  ·
                    rfl

theorem cell22_3185877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_3185877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185877 prefixEnd_3185877 := by exact prefixLift 3185877
  have htrace : WordTrace (prefixWord ++ tailWord_3185877) baseStart_3185877 baseEnd_3185877 := by
    simpa [prefixWord, tailWord_3185877, baseEnd_3185877] using wordTrace_append hprefix tailTrace_3185877
  have hstable : (prefixWord ++ tailWord_3185877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185877).length < 2 ^ (prefixWord ++ tailWord_3185877).sum := by decide
  have hdescent : baseEnd_3185877 < baseStart_3185877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185905 : List Nat := [1, 2, 2, 2, 2, 1, 1, 7, 4]
def baseStart_3185905 : Nat := 118140960795 + 3185905 * 2 ^ 59
def prefixEnd_3185905 : Nat := 4983230072969 + 3 ^ 40 * 3185905 * 2
def baseEnd_3185905 : Nat := 363533463236102859052399

theorem tailTrace_3185905 : CollatzResearch.WordTrace tailWord_3185905 prefixEnd_3185905 363533463236102859052399 := by
  unfold tailWord_3185905
  simp only [CollatzResearch.WordTrace]
  refine ⟨116199501523017769100359169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77466334348678512733572779 116199501523017769100359169)
  ·
    refine ⟨87149626142263326825269377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116199501523017769100359169 87149626142263326825269377)
    ·
      refine ⟨65362219606697495118952033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87149626142263326825269377 65362219606697495118952033)
      ·
        refine ⟨49021664705023121339214025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65362219606697495118952033 49021664705023121339214025)
        ·
          refine ⟨36766248528767341004410519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49021664705023121339214025 36766248528767341004410519)
          ·
            refine ⟨55149372793151011506615779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36766248528767341004410519 55149372793151011506615779)
            ·
              refine ⟨82724059189726517259923669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55149372793151011506615779 82724059189726517259923669)
              ·
                refine ⟨1938845137259215248279461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 82724059189726517259923669 1938845137259215248279461)
                ·
                  refine ⟨363533463236102859052399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1938845137259215248279461 363533463236102859052399)
                  ·
                    rfl

theorem cell22_3185905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 4].length) (baseStart_3185905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185905 prefixEnd_3185905 := by exact prefixLift 3185905
  have htrace : WordTrace (prefixWord ++ tailWord_3185905) baseStart_3185905 baseEnd_3185905 := by
    simpa [prefixWord, tailWord_3185905, baseEnd_3185905] using wordTrace_append hprefix tailTrace_3185905
  have hstable : (prefixWord ++ tailWord_3185905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185905).length < 2 ^ (prefixWord ++ tailWord_3185905).sum := by decide
  have hdescent : baseEnd_3185905 < baseStart_3185905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185907 : List Nat := [1, 1, 1, 2, 2, 6, 3, 1, 1, 4]
def baseStart_3185907 : Nat := 118140960795 + 3185907 * 2 ^ 59
def prefixEnd_3185907 : Nat := 4983230072969 + 3 ^ 40 * 3185907 * 2
def baseEnd_3185907 : Nat := 1090601074349181238607191

theorem tailTrace_3185907 : CollatzResearch.WordTrace tailWord_3185907 prefixEnd_3185907 1090601074349181238607191 := by
  unfold tailWord_3185907
  simp only [CollatzResearch.WordTrace]
  refine ⟨116199574469010523441931975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77466382979340348961287983 116199574469010523441931975)
  ·
    refine ⟨174299361703515785162897963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116199574469010523441931975 174299361703515785162897963)
    ·
      refine ⟨261449042555273677744346945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174299361703515785162897963 261449042555273677744346945)
      ·
        refine ⟨196086781916455258308260209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261449042555273677744346945 196086781916455258308260209)
        ·
          refine ⟨147065086437341443731195157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196086781916455258308260209 147065086437341443731195157)
          ·
            refine ⟨6893675926750380174899773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147065086437341443731195157 6893675926750380174899773)
            ·
              refine ⟨2585128472531392565587415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6893675926750380174899773 2585128472531392565587415)
              ·
                refine ⟨3877692708797088848381123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585128472531392565587415 3877692708797088848381123)
                ·
                  refine ⟨5816539063195633272571685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877692708797088848381123 5816539063195633272571685)
                  ·
                    refine ⟨1090601074349181238607191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5816539063195633272571685 1090601074349181238607191)
                    ·
                      rfl

theorem cell22_3185907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 1, 4].length) (baseStart_3185907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185907 prefixEnd_3185907 := by exact prefixLift 3185907
  have htrace : WordTrace (prefixWord ++ tailWord_3185907) baseStart_3185907 baseEnd_3185907 := by
    simpa [prefixWord, tailWord_3185907, baseEnd_3185907] using wordTrace_append hprefix tailTrace_3185907
  have hstable : (prefixWord ++ tailWord_3185907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185907).length < 2 ^ (prefixWord ++ tailWord_3185907).sum := by decide
  have hdescent : baseEnd_3185907 < baseStart_3185907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186016 : List Nat := [2, 1, 1, 3, 4, 3, 1, 3, 1, 3]
def baseStart_3186016 : Nat := 118140960795 + 3186016 * 2 ^ 59
def prefixEnd_3186016 : Nat := 4983230072969 + 3 ^ 40 * 3186016 * 2
def baseEnd_3186016 : Nat := 1090638387276741287631857

theorem tailTrace_3186016 : CollatzResearch.WordTrace tailWord_3186016 prefixEnd_3186016 1090638387276741287631857 := by
  unfold tailWord_3186016
  simp only [CollatzResearch.WordTrace]
  refine ⟨58101775012807817528824951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77469033350410423371766601 58101775012807817528824951)
  ·
    refine ⟨87152662519211726293237427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58101775012807817528824951 87152662519211726293237427)
    ·
      refine ⟨130728993778817589439856141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87152662519211726293237427 130728993778817589439856141)
      ·
        refine ⟨49023372667056596039946053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130728993778817589439856141 49023372667056596039946053)
        ·
          refine ⟨9191882375073111757489885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49023372667056596039946053 9191882375073111757489885)
          ·
            refine ⟨3446955890652416909058707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9191882375073111757489885 3446955890652416909058707)
            ·
              refine ⟨5170433835978625363588061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446955890652416909058707 5170433835978625363588061)
              ·
                refine ⟨1938912688491984511345523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5170433835978625363588061 1938912688491984511345523)
                ·
                  refine ⟨2908369032737976767018285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938912688491984511345523 2908369032737976767018285)
                  ·
                    refine ⟨1090638387276741287631857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2908369032737976767018285 1090638387276741287631857)
                    ·
                      rfl

theorem cell22_3186016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 1, 3].length) (baseStart_3186016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186016 prefixEnd_3186016 := by exact prefixLift 3186016
  have htrace : WordTrace (prefixWord ++ tailWord_3186016) baseStart_3186016 baseEnd_3186016 := by
    simpa [prefixWord, tailWord_3186016, baseEnd_3186016] using wordTrace_append hprefix tailTrace_3186016
  have hstable : (prefixWord ++ tailWord_3186016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186016).length < 2 ^ (prefixWord ++ tailWord_3186016).sum := by decide
  have hdescent : baseEnd_3186016 < baseStart_3186016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186046 : List Nat := [4, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_3186046 : Nat := 118140960795 + 3186046 * 2 ^ 59
def prefixEnd_3186046 : Nat := 4983230072969 + 3 ^ 40 * 3186046 * 2
def baseEnd_3186046 : Nat := 363549552296610403127255

theorem tailTrace_3186046 : CollatzResearch.WordTrace tailWord_3186046 prefixEnd_3186046 363549552296610403127255 := by
  unfold tailWord_3186046
  simp only [CollatzResearch.WordTrace]
  refine ⟨14525580526938368772655249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77469762810337966787494661 14525580526938368772655249)
  ·
    refine ⟨10894185395203776579491437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14525580526938368772655249 10894185395203776579491437)
    ·
      refine ⟨4085319523201416217309289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10894185395203776579491437 4085319523201416217309289)
      ·
        refine ⟨3063989642401062162981967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4085319523201416217309289 3063989642401062162981967)
        ·
          refine ⟨4595984463601593244472951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3063989642401062162981967 4595984463601593244472951)
          ·
            refine ⟨6893976695402389866709427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595984463601593244472951 6893976695402389866709427)
            ·
              refine ⟨10340965043103584800064141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6893976695402389866709427 10340965043103584800064141)
              ·
                refine ⟨3877861891163844300024053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10340965043103584800064141 3877861891163844300024053)
                ·
                  refine ⟨363549552296610403127255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3877861891163844300024053 363549552296610403127255)
                  ·
                    rfl

theorem cell22_3186046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_3186046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186046 prefixEnd_3186046 := by exact prefixLift 3186046
  have htrace : WordTrace (prefixWord ++ tailWord_3186046) baseStart_3186046 baseEnd_3186046 := by
    simpa [prefixWord, tailWord_3186046, baseEnd_3186046] using wordTrace_append hprefix tailTrace_3186046
  have hstable : (prefixWord ++ tailWord_3186046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186046).length < 2 ^ (prefixWord ++ tailWord_3186046).sum := by decide
  have hdescent : baseEnd_3186046 < baseStart_3186046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186087 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3186087 : Nat := 118140960795 + 3186087 * 2 ^ 59
def prefixEnd_3186087 : Nat := 4983230072969 + 3 ^ 40 * 3186087 * 2
def baseEnd_3186087 : Nat := 1090662692027720769106639

theorem tailTrace_3186087 : CollatzResearch.WordTrace tailWord_3186087 prefixEnd_3186087 1090662692027720769106639 := by
  unfold tailWord_3186087
  simp only [CollatzResearch.WordTrace]
  refine ⟨116206139608358414183484515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77470759738905609455656343 116206139608358414183484515)
  ·
    refine ⟨174309209412537621275226773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116206139608358414183484515 174309209412537621275226773)
    ·
      refine ⟨8170744191212700997276255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174309209412537621275226773 8170744191212700997276255)
      ·
        refine ⟨12256116286819051495914383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8170744191212700997276255 12256116286819051495914383)
        ·
          refine ⟨18384174430228577243871575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12256116286819051495914383 18384174430228577243871575)
          ·
            refine ⟨27576261645342865865807363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18384174430228577243871575 27576261645342865865807363)
            ·
              refine ⟨41364392468014298798711045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27576261645342865865807363 41364392468014298798711045)
              ·
                refine ⟨7755823587752681024758321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41364392468014298798711045 7755823587752681024758321)
                ·
                  refine ⟨5816867690814510768568741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7755823587752681024758321 5816867690814510768568741)
                  ·
                    refine ⟨1090662692027720769106639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5816867690814510768568741 1090662692027720769106639)
                    ·
                      rfl

theorem cell22_3186087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3186087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186087 prefixEnd_3186087 := by exact prefixLift 3186087
  have htrace : WordTrace (prefixWord ++ tailWord_3186087) baseStart_3186087 baseEnd_3186087 := by
    simpa [prefixWord, tailWord_3186087, baseEnd_3186087] using wordTrace_append hprefix tailTrace_3186087
  have hstable : (prefixWord ++ tailWord_3186087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186087).length < 2 ^ (prefixWord ++ tailWord_3186087).sum := by decide
  have hdescent : baseEnd_3186087 < baseStart_3186087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186147 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 7]
def baseStart_3186147 : Nat := 118140960795 + 3186147 * 2 ^ 59
def prefixEnd_3186147 : Nat := 4983230072969 + 3 ^ 40 * 3186147 * 2
def baseEnd_3186147 : Nat := 363561077084633537535485

theorem tailTrace_3186147 : CollatzResearch.WordTrace tailWord_3186147 prefixEnd_3186147 363561077084633537535485 := by
  unfold tailWord_3186147
  simp only [CollatzResearch.WordTrace]
  refine ⟨116208327988141044430668695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77472218658760696287112463 116208327988141044430668695)
  ·
    refine ⟨174312491982211566646003043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116208327988141044430668695 174312491982211566646003043)
    ·
      refine ⟨261468737973317349969004565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174312491982211566646003043 261468737973317349969004565)
      ·
        refine ⟨12256347092499250779797089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 261468737973317349969004565 12256347092499250779797089)
        ·
          refine ⟨9192260319374438084847817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12256347092499250779797089 9192260319374438084847817)
          ·
            refine ⟨6894195239530828563635863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9192260319374438084847817 6894195239530828563635863)
            ·
              refine ⟨10341292859296242845453795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6894195239530828563635863 10341292859296242845453795)
              ·
                refine ⟨15511939288944364268180693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10341292859296242845453795 15511939288944364268180693)
                ·
                  refine ⟨363561077084633537535485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15511939288944364268180693 363561077084633537535485)
                  ·
                    rfl

theorem cell22_3186147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 7].length) (baseStart_3186147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186147 prefixEnd_3186147 := by exact prefixLift 3186147
  have htrace : WordTrace (prefixWord ++ tailWord_3186147) baseStart_3186147 baseEnd_3186147 := by
    simpa [prefixWord, tailWord_3186147, baseEnd_3186147] using wordTrace_append hprefix tailTrace_3186147
  have hstable : (prefixWord ++ tailWord_3186147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186147).length < 2 ^ (prefixWord ++ tailWord_3186147).sum := by decide
  have hdescent : baseEnd_3186147 < baseStart_3186147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186151 : List Nat := [1, 1, 5, 2, 1, 2, 2, 4, 1, 3]
def baseStart_3186151 : Nat := 118140960795 + 3186151 * 2 ^ 59
def prefixEnd_3186151 : Nat := 4983230072969 + 3 ^ 40 * 3186151 * 2
def baseEnd_3186151 : Nat := 1090684600535645935506443

theorem tailTrace_3186151 : CollatzResearch.WordTrace tailWord_3186151 prefixEnd_3186151 1090684600535645935506443 := by
  unfold tailWord_3186151
  simp only [CollatzResearch.WordTrace]
  refine ⟨116208473880126553113814307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77472315920084368742542871 116208473880126553113814307)
  ·
    refine ⟨174312710820189829670721461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116208473880126553113814307 174312710820189829670721461)
    ·
      refine ⟨16341816639392796531630137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174312710820189829670721461 16341816639392796531630137)
      ·
        refine ⟨12256362479544597398722603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16341816639392796531630137 12256362479544597398722603)
        ·
          refine ⟨18384543719316896098083905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12256362479544597398722603 18384543719316896098083905)
          ·
            refine ⟨13788407789487672073562929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18384543719316896098083905 13788407789487672073562929)
            ·
              refine ⟨10341305842115754055172197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13788407789487672073562929 10341305842115754055172197)
              ·
                refine ⟨1938994845396703885344787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10341305842115754055172197 1938994845396703885344787)
                ·
                  refine ⟨2908492268095055828017181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938994845396703885344787 2908492268095055828017181)
                  ·
                    refine ⟨1090684600535645935506443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2908492268095055828017181 1090684600535645935506443)
                    ·
                      rfl

theorem cell22_3186151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_3186151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186151 prefixEnd_3186151 := by exact prefixLift 3186151
  have htrace : WordTrace (prefixWord ++ tailWord_3186151) baseStart_3186151 baseEnd_3186151 := by
    simpa [prefixWord, tailWord_3186151, baseEnd_3186151] using wordTrace_append hprefix tailTrace_3186151
  have hstable : (prefixWord ++ tailWord_3186151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186151).length < 2 ^ (prefixWord ++ tailWord_3186151).sum := by decide
  have hdescent : baseEnd_3186151 < baseStart_3186151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186175 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 8]
def baseStart_3186175 : Nat := 118140960795 + 3186175 * 2 ^ 59
def prefixEnd_3186175 : Nat := 4983230072969 + 3 ^ 40 * 3186175 * 2
def baseEnd_3186175 : Nat := 363564272075372624302123

theorem tailTrace_3186175 : CollatzResearch.WordTrace tailWord_3186175 prefixEnd_3186175 363564272075372624302123 := by
  unfold tailWord_3186175
  simp only [CollatzResearch.WordTrace]
  refine ⟨116209349232039605212687979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77472899488026403475125319 116209349232039605212687979)
  ·
    refine ⟨174314023848059407819031969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116209349232039605212687979 174314023848059407819031969)
    ·
      refine ⟨130735517886044555864273977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174314023848059407819031969 130735517886044555864273977)
      ·
        refine ⟨98051638414533416898205483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130735517886044555864273977 98051638414533416898205483)
        ·
          refine ⟨147077457621800125347308225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98051638414533416898205483 147077457621800125347308225)
          ·
            refine ⟨110308093216350094010481169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147077457621800125347308225 110308093216350094010481169)
            ·
              refine ⟨82731069912262570507860877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110308093216350094010481169 82731069912262570507860877)
              ·
                refine ⟨31024151217098463940447829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82731069912262570507860877 31024151217098463940447829)
                ·
                  refine ⟨363564272075372624302123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31024151217098463940447829 363564272075372624302123)
                  ·
                    rfl

theorem cell22_3186175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 8].length) (baseStart_3186175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186175 prefixEnd_3186175 := by exact prefixLift 3186175
  have htrace : WordTrace (prefixWord ++ tailWord_3186175) baseStart_3186175 baseEnd_3186175 := by
    simpa [prefixWord, tailWord_3186175, baseEnd_3186175] using wordTrace_append hprefix tailTrace_3186175
  have hstable : (prefixWord ++ tailWord_3186175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186175).length < 2 ^ (prefixWord ++ tailWord_3186175).sum := by decide
  have hdescent : baseEnd_3186175 < baseStart_3186175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186209 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 6]
def baseStart_3186209 : Nat := 118140960795 + 3186209 * 2 ^ 59
def prefixEnd_3186209 : Nat := 4983230072969 + 3 ^ 40 * 3186209 * 2
def baseEnd_3186209 : Nat := 363568151706984372518755

theorem tailTrace_3186209 : CollatzResearch.WordTrace tailWord_3186209 prefixEnd_3186209 363568151706984372518755 := by
  unfold tailWord_3186209
  simp only [CollatzResearch.WordTrace]
  refine ⟨116210589313916429019425681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77473726209277619346283787 116210589313916429019425681)
  ·
    refine ⟨87157941985437321764569261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116210589313916429019425681 87157941985437321764569261)
    ·
      refine ⟨32684228244538995661713473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87157941985437321764569261 32684228244538995661713473)
      ·
        refine ⟨24513171183404246746285105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32684228244538995661713473 24513171183404246746285105)
        ·
          refine ⟨18384878387553185059713829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24513171183404246746285105 18384878387553185059713829)
          ·
            refine ⟨3447164697666222198696343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18384878387553185059713829 3447164697666222198696343)
            ·
              refine ⟨5170747046499333298044515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447164697666222198696343 5170747046499333298044515)
              ·
                refine ⟨7756120569748999947066773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170747046499333298044515 7756120569748999947066773)
                ·
                  refine ⟨363568151706984372518755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7756120569748999947066773 363568151706984372518755)
                  ·
                    rfl

theorem cell22_3186209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 6].length) (baseStart_3186209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186209 prefixEnd_3186209 := by exact prefixLift 3186209
  have htrace : WordTrace (prefixWord ++ tailWord_3186209) baseStart_3186209 baseEnd_3186209 := by
    simpa [prefixWord, tailWord_3186209, baseEnd_3186209] using wordTrace_append hprefix tailTrace_3186209
  have hstable : (prefixWord ++ tailWord_3186209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186209).length < 2 ^ (prefixWord ++ tailWord_3186209).sum := by decide
  have hdescent : baseEnd_3186209 < baseStart_3186209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186239 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 2, 4]
def baseStart_3186239 : Nat := 118140960795 + 3186239 * 2 ^ 59
def prefixEnd_3186239 : Nat := 4983230072969 + 3 ^ 40 * 3186239 * 2
def baseEnd_3186239 : Nat := 1090714724734043039306173

theorem tailTrace_3186239 : CollatzResearch.WordTrace tailWord_3186239 prefixEnd_3186239 1090714724734043039306173 := by
  unfold tailWord_3186239
  simp only [CollatzResearch.WordTrace]
  refine ⟨116211683503807744143017771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77474455669205162762011847 116211683503807744143017771)
  ·
    refine ⟨174317525255711616214526657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116211683503807744143017771 174317525255711616214526657)
    ·
      refine ⟨130738143941783712160894993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174317525255711616214526657 130738143941783712160894993)
      ·
        refine ⟨98053607956337784120671245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130738143941783712160894993 98053607956337784120671245)
        ·
          refine ⟨36770102983626669045251717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98053607956337784120671245 36770102983626669045251717)
          ·
            refine ⟨6894394309430000445984697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36770102983626669045251717 6894394309430000445984697)
            ·
              refine ⟨5170795732072500334488523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6894394309430000445984697 5170795732072500334488523)
              ·
                refine ⟨7756193598108750501732785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170795732072500334488523 7756193598108750501732785)
                ·
                  refine ⟨5817145198581562876299589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7756193598108750501732785 5817145198581562876299589)
                  ·
                    refine ⟨1090714724734043039306173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5817145198581562876299589 1090714724734043039306173)
                    ·
                      rfl

theorem cell22_3186239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_3186239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186239 prefixEnd_3186239 := by exact prefixLift 3186239
  have htrace : WordTrace (prefixWord ++ tailWord_3186239) baseStart_3186239 baseEnd_3186239 := by
    simpa [prefixWord, tailWord_3186239, baseEnd_3186239] using wordTrace_append hprefix tailTrace_3186239
  have hstable : (prefixWord ++ tailWord_3186239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186239).length < 2 ^ (prefixWord ++ tailWord_3186239).sum := by decide
  have hdescent : baseEnd_3186239 < baseStart_3186239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186297 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 1, 7]
def baseStart_3186297 : Nat := 118140960795 + 3186297 * 2 ^ 59
def prefixEnd_3186297 : Nat := 4983230072969 + 3 ^ 40 * 3186297 * 2
def baseEnd_3186297 : Nat := 1090734579319350221355995

theorem tailTrace_3186297 : CollatzResearch.WordTrace tailWord_3186297 prefixEnd_3186297 1090734579319350221355995 := by
  unfold tailWord_3186297
  simp only [CollatzResearch.WordTrace]
  refine ⟨116213798937597620048629145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77475865958398413365752763 116213798937597620048629145)
  ·
    refine ⟨87160349203198215036471859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116213798937597620048629145 87160349203198215036471859)
    ·
      refine ⟨130740523804797322554707789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87160349203198215036471859 130740523804797322554707789)
      ·
        refine ⟨49027696426798995958015421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130740523804797322554707789 49027696426798995958015421)
        ·
          refine ⟨18385386160049623484255783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49027696426798995958015421 18385386160049623484255783)
          ·
            refine ⟨27578079240074435226383675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18385386160049623484255783 27578079240074435226383675)
            ·
              refine ⟨41367118860111652839575513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27578079240074435226383675 41367118860111652839575513)
              ·
                refine ⟨31025339145083739629681635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41367118860111652839575513 31025339145083739629681635)
                ·
                  refine ⟨46538008717625609444522453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31025339145083739629681635 46538008717625609444522453)
                  ·
                    refine ⟨1090734579319350221355995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46538008717625609444522453 1090734579319350221355995)
                    ·
                      rfl

theorem cell22_3186297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_3186297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186297 prefixEnd_3186297 := by exact prefixLift 3186297
  have htrace : WordTrace (prefixWord ++ tailWord_3186297) baseStart_3186297 baseEnd_3186297 := by
    simpa [prefixWord, tailWord_3186297, baseEnd_3186297] using wordTrace_append hprefix tailTrace_3186297
  have hstable : (prefixWord ++ tailWord_3186297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186297).length < 2 ^ (prefixWord ++ tailWord_3186297).sum := by decide
  have hdescent : baseEnd_3186297 < baseStart_3186297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186314 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_3186314 : Nat := 118140960795 + 3186314 * 2 ^ 59
def prefixEnd_3186314 : Nat := 4983230072969 + 3 ^ 40 * 3186314 * 2
def baseEnd_3186314 : Nat := 1090740398766767843680943

theorem tailTrace_3186314 : CollatzResearch.WordTrace tailWord_3186314 prefixEnd_3186314 1090740398766767843680943 := by
  unfold tailWord_3186314
  simp only [CollatzResearch.WordTrace]
  refine ⟨29053604744634007987999499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77476279319024021301331997 29053604744634007987999499)
  ·
    refine ⟨43580407116951011981999249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29053604744634007987999499 43580407116951011981999249)
    ·
      refine ⟨32685305337713258986499437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43580407116951011981999249 32685305337713258986499437)
      ·
        refine ⟨12256989501642472119937289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32685305337713258986499437 12256989501642472119937289)
        ·
          refine ⟨9192742126231854089952967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12256989501642472119937289 9192742126231854089952967)
          ·
            refine ⟨13789113189347781134929451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9192742126231854089952967 13789113189347781134929451)
            ·
              refine ⟨20683669784021671702394177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13789113189347781134929451 20683669784021671702394177)
              ·
                refine ⟨15512752338016253776795633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20683669784021671702394177 15512752338016253776795633)
                ·
                  refine ⟨11634564253512190332596725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15512752338016253776795633 11634564253512190332596725)
                  ·
                    refine ⟨1090740398766767843680943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11634564253512190332596725 1090740398766767843680943)
                    ·
                      rfl

theorem cell22_3186314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_3186314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186314 prefixEnd_3186314 := by exact prefixLift 3186314
  have htrace : WordTrace (prefixWord ++ tailWord_3186314) baseStart_3186314 baseEnd_3186314 := by
    simpa [prefixWord, tailWord_3186314, baseEnd_3186314] using wordTrace_append hprefix tailTrace_3186314
  have hstable : (prefixWord ++ tailWord_3186314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186314).length < 2 ^ (prefixWord ++ tailWord_3186314).sum := by decide
  have hdescent : baseEnd_3186314 < baseStart_3186314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186361 : List Nat := [1, 2, 1, 4, 1, 1, 5, 3, 4]
def baseStart_3186361 : Nat := 118140960795 + 3186361 * 2 ^ 59
def prefixEnd_3186361 : Nat := 4983230072969 + 3 ^ 40 * 3186361 * 2
def baseEnd_3186361 : Nat := 363585495942425129251933

theorem tailTrace_3186361 : CollatzResearch.WordTrace tailWord_3186361 prefixEnd_3186361 363585495942425129251933 := by
  unfold tailWord_3186361
  simp only [CollatzResearch.WordTrace]
  refine ⟨116216133209365758978958937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77477422139577172652639291 116216133209365758978958937)
  ·
    refine ⟨87162099907024319234219203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116216133209365758978958937 87162099907024319234219203)
    ·
      refine ⟨130743149860536478851328805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87162099907024319234219203 130743149860536478851328805)
      ·
        refine ⟨24514340598850589784624151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130743149860536478851328805 24514340598850589784624151)
        ·
          refine ⟨36771510898275884676936227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24514340598850589784624151 36771510898275884676936227)
          ·
            refine ⟨55157266347413827015404341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36771510898275884676936227 55157266347413827015404341)
            ·
              refine ⟨5170993720070046282694157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55157266347413827015404341 5170993720070046282694157)
              ·
                refine ⟨1939122645026267356010309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5170993720070046282694157 1939122645026267356010309)
                ·
                  refine ⟨363585495942425129251933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1939122645026267356010309 363585495942425129251933)
                  ·
                    rfl

theorem cell22_3186361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 4].length) (baseStart_3186361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186361 prefixEnd_3186361 := by exact prefixLift 3186361
  have htrace : WordTrace (prefixWord ++ tailWord_3186361) baseStart_3186361 baseEnd_3186361 := by
    simpa [prefixWord, tailWord_3186361, baseEnd_3186361] using wordTrace_append hprefix tailTrace_3186361
  have hstable : (prefixWord ++ tailWord_3186361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186361).length < 2 ^ (prefixWord ++ tailWord_3186361).sum := by decide
  have hdescent : baseEnd_3186361 < baseStart_3186361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186376 : List Nat := [2, 1, 3, 1, 2, 2, 2, 4, 2, 3]
def baseStart_3186376 : Nat := 118140960795 + 3186376 * 2 ^ 59
def prefixEnd_3186376 : Nat := 4983230072969 + 3 ^ 40 * 3186376 * 2
def baseEnd_3186376 : Nat := 1090761622633820348630753

theorem tailTrace_3186376 : CollatzResearch.WordTrace tailWord_3186376 prefixEnd_3186376 1090761622633820348630753 := by
  unfold tailWord_3186376
  simp only [CollatzResearch.WordTrace]
  refine ⟨58108340152155708270377491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77477786869540944360503321 58108340152155708270377491)
  ·
    refine ⟨87162510228233562405566237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58108340152155708270377491 87162510228233562405566237)
    ·
      refine ⟨32685941335587585902087339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87162510228233562405566237 32685941335587585902087339)
      ·
        refine ⟨49028912003381378853131009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32685941335587585902087339 49028912003381378853131009)
        ·
          refine ⟨36771684002536034139848257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49028912003381378853131009 36771684002536034139848257)
          ·
            refine ⟨27578763001902025604886193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36771684002536034139848257 27578763001902025604886193)
            ·
              refine ⟨20684072251426519203664645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27578763001902025604886193 20684072251426519203664645)
              ·
                refine ⟨3878263547142472350687121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20684072251426519203664645 3878263547142472350687121)
                ·
                  refine ⟨2908697660356854263015341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3878263547142472350687121 2908697660356854263015341)
                  ·
                    refine ⟨1090761622633820348630753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2908697660356854263015341 1090761622633820348630753)
                    ·
                      rfl

theorem cell22_3186376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_3186376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186376 prefixEnd_3186376 := by exact prefixLift 3186376
  have htrace : WordTrace (prefixWord ++ tailWord_3186376) baseStart_3186376 baseEnd_3186376 := by
    simpa [prefixWord, tailWord_3186376, baseEnd_3186376] using wordTrace_append hprefix tailTrace_3186376
  have hstable : (prefixWord ++ tailWord_3186376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186376).length < 2 ^ (prefixWord ++ tailWord_3186376).sum := by decide
  have hdescent : baseEnd_3186376 < baseStart_3186376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186378 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 6]
def baseStart_3186378 : Nat := 118140960795 + 3186378 * 2 ^ 59
def prefixEnd_3186378 : Nat := 4983230072969 + 3 ^ 40 * 3186378 * 2
def baseEnd_3186378 : Nat := 363587435758231003360249

theorem tailTrace_3186378 : CollatzResearch.WordTrace tailWord_3186378 prefixEnd_3186378 363587435758231003360249 := by
  unfold tailWord_3186378
  simp only [CollatzResearch.WordTrace]
  refine ⟨29054188312576042720581947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77477835500202780588218525 29054188312576042720581947)
  ·
    refine ⟨43581282468864064080872921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29054188312576042720581947 43581282468864064080872921)
    ·
      refine ⟨32685961851648048060654691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43581282468864064080872921 32685961851648048060654691)
      ·
        refine ⟨49028942777472072090982037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32685961851648048060654691 49028942777472072090982037)
        ·
          refine ⟨2298231692694003379264783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49028942777472072090982037 2298231692694003379264783)
          ·
            refine ⟨3447347539041005068897175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298231692694003379264783 3447347539041005068897175)
            ·
              refine ⟨5171021308561507603345763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447347539041005068897175 5171021308561507603345763)
              ·
                refine ⟨7756531962842261405018645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171021308561507603345763 7756531962842261405018645)
                ·
                  refine ⟨363587435758231003360249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7756531962842261405018645 363587435758231003360249)
                  ·
                    rfl

theorem cell22_3186378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_3186378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186378 prefixEnd_3186378 := by exact prefixLift 3186378
  have htrace : WordTrace (prefixWord ++ tailWord_3186378) baseStart_3186378 baseEnd_3186378 := by
    simpa [prefixWord, tailWord_3186378, baseEnd_3186378] using wordTrace_append hprefix tailTrace_3186378
  have hstable : (prefixWord ++ tailWord_3186378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186378).length < 2 ^ (prefixWord ++ tailWord_3186378).sum := by decide
  have hdescent : baseEnd_3186378 < baseStart_3186378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186387 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 3, 9]
def baseStart_3186387 : Nat := 118140960795 + 3186387 * 2 ^ 59
def prefixEnd_3186387 : Nat := 4983230072969 + 3 ^ 40 * 3186387 * 2
def baseEnd_3186387 : Nat := 1090765388158619986605719

theorem tailTrace_3186387 : CollatzResearch.WordTrace tailWord_3186387 prefixEnd_3186387 1090765388158619986605719 := by
  unfold tailWord_3186387
  simp only [CollatzResearch.WordTrace]
  refine ⟨116217081507271565419405415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77478054338181043612936943 116217081507271565419405415)
  ·
    refine ⟨174325622260907348129108123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116217081507271565419405415 174325622260907348129108123)
    ·
      refine ⟨261488433391361022193662185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174325622260907348129108123 261488433391361022193662185)
      ·
        refine ⟨196116325043520766645246639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261488433391361022193662185 196116325043520766645246639)
        ·
          refine ⟨294174487565281149967869959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196116325043520766645246639 294174487565281149967869959)
          ·
            refine ⟨441261731347921724951804939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294174487565281149967869959 441261731347921724951804939)
            ·
              refine ⟨661892597021882587427707409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441261731347921724951804939 661892597021882587427707409)
              ·
                refine ⟨496419447766411940570780557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661892597021882587427707409 496419447766411940570780557)
                ·
                  refine ⟨186157292912404477714042709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496419447766411940570780557 186157292912404477714042709)
                  ·
                    refine ⟨1090765388158619986605719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 186157292912404477714042709 1090765388158619986605719)
                    ·
                      rfl

theorem cell22_3186387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_3186387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186387 prefixEnd_3186387 := by exact prefixLift 3186387
  have htrace : WordTrace (prefixWord ++ tailWord_3186387) baseStart_3186387 baseEnd_3186387 := by
    simpa [prefixWord, tailWord_3186387, baseEnd_3186387] using wordTrace_append hprefix tailTrace_3186387
  have hstable : (prefixWord ++ tailWord_3186387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186387).length < 2 ^ (prefixWord ++ tailWord_3186387).sum := by decide
  have hdescent : baseEnd_3186387 < baseStart_3186387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186393 : List Nat := [1, 2, 1, 2, 3, 3, 4, 1, 2, 3]
def baseStart_3186393 : Nat := 118140960795 + 3186393 * 2 ^ 59
def prefixEnd_3186393 : Nat := 4983230072969 + 3 ^ 40 * 3186393 * 2
def baseEnd_3186393 : Nat := 1090767442081237970955701

theorem tailTrace_3186393 : CollatzResearch.WordTrace tailWord_3186393 prefixEnd_3186393 1090767442081237970955701 := by
  unfold tailWord_3186393
  simp only [CollatzResearch.WordTrace]
  refine ⟨116217300345249828444123833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77478200230166552296082555 116217300345249828444123833)
  ·
    refine ⟨87162975258937371333092875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116217300345249828444123833 87162975258937371333092875)
    ·
      refine ⟨130744462888406056999639313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87162975258937371333092875 130744462888406056999639313)
      ·
        refine ⟨98058347166304542749729485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130744462888406056999639313 98058347166304542749729485)
        ·
          refine ⟨36771880187364203531148557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98058347166304542749729485 36771880187364203531148557)
          ·
            refine ⟨13789455070261576324180709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36771880187364203531148557 13789455070261576324180709)
            ·
              refine ⟨2585522825674045560783883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13789455070261576324180709 2585522825674045560783883)
              ·
                refine ⟨3878284238511068341175825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585522825674045560783883 3878284238511068341175825)
                ·
                  refine ⟨2908713178883301255881869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3878284238511068341175825 2908713178883301255881869)
                  ·
                    refine ⟨1090767442081237970955701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2908713178883301255881869 1090767442081237970955701)
                    ·
                      rfl

theorem cell22_3186393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 2, 3].length) (baseStart_3186393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186393 prefixEnd_3186393 := by exact prefixLift 3186393
  have htrace : WordTrace (prefixWord ++ tailWord_3186393) baseStart_3186393 baseEnd_3186393 := by
    simpa [prefixWord, tailWord_3186393, baseEnd_3186393] using wordTrace_append hprefix tailTrace_3186393
  have hstable : (prefixWord ++ tailWord_3186393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186393).length < 2 ^ (prefixWord ++ tailWord_3186393).sum := by decide
  have hdescent : baseEnd_3186393 < baseStart_3186393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186397 : List Nat := [1, 4, 3, 3, 2, 1, 1, 2, 1, 4]
def baseStart_3186397 : Nat := 118140960795 + 3186397 * 2 ^ 59
def prefixEnd_3186397 : Nat := 4983230072969 + 3 ^ 40 * 3186397 * 2
def baseEnd_3186397 : Nat := 1090768811362983293855689

theorem tailTrace_3186397 : CollatzResearch.WordTrace tailWord_3186397 prefixEnd_3186397 1090768811362983293855689 := by
  unfold tailWord_3186397
  simp only [CollatzResearch.WordTrace]
  refine ⟨116217446237235337127269445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77478297491490224751512963 116217446237235337127269445)
  ·
    refine ⟨21790771169481625711363021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116217446237235337127269445 21790771169481625711363021)
    ·
      refine ⟨8171539188555609641761133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21790771169481625711363021 8171539188555609641761133)
      ·
        refine ⟨3064327195708353615660425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8171539188555609641761133 3064327195708353615660425)
        ·
          refine ⟨2298245396781265211745319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3064327195708353615660425 2298245396781265211745319)
          ·
            refine ⟨3447368095171897817617979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298245396781265211745319 3447368095171897817617979)
            ·
              refine ⟨5171052142757846726426969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447368095171897817617979 5171052142757846726426969)
              ·
                refine ⟨3878289107068385044820227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5171052142757846726426969 3878289107068385044820227)
                ·
                  refine ⟨5817433660602577567230341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3878289107068385044820227 5817433660602577567230341)
                  ·
                    refine ⟨1090768811362983293855689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5817433660602577567230341 1090768811362983293855689)
                    ·
                      rfl

theorem cell22_3186397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_3186397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186397 prefixEnd_3186397 := by exact prefixLift 3186397
  have htrace : WordTrace (prefixWord ++ tailWord_3186397) baseStart_3186397 baseEnd_3186397 := by
    simpa [prefixWord, tailWord_3186397, baseEnd_3186397] using wordTrace_append hprefix tailTrace_3186397
  have hstable : (prefixWord ++ tailWord_3186397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186397).length < 2 ^ (prefixWord ++ tailWord_3186397).sum := by decide
  have hdescent : baseEnd_3186397 < baseStart_3186397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186485 : List Nat := [1, 3, 3, 1, 5, 1, 1, 2, 5]
def baseStart_3186485 : Nat := 118140960795 + 3186485 * 2 ^ 59
def prefixEnd_3186485 : Nat := 4983230072969 + 3 ^ 40 * 3186485 * 2
def baseEnd_3186485 : Nat := 363599645187126799218473

theorem tailTrace_3186485 : CollatzResearch.WordTrace tailWord_3186485 prefixEnd_3186485 363599645187126799218473 := by
  unfold tailWord_3186485
  simp only [CollatzResearch.WordTrace]
  refine ⟨116220655860916528156472909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77480437240611018770981939 116220655860916528156472909)
  ·
    refine ⟨43582745947843698058677341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116220655860916528156472909 43582745947843698058677341)
    ·
      refine ⟨16343529730441386772004003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43582745947843698058677341 16343529730441386772004003)
      ·
        refine ⟨24515294595662080158006005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16343529730441386772004003 24515294595662080158006005)
        ·
          refine ⟨2298308868343320014813063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24515294595662080158006005 2298308868343320014813063)
          ·
            refine ⟨3447463302514980022219595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298308868343320014813063 3447463302514980022219595)
            ·
              refine ⟨5171194953772470033329393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447463302514980022219595 5171194953772470033329393)
              ·
                refine ⟨3878396215329352524997045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5171194953772470033329393 3878396215329352524997045)
                ·
                  refine ⟨363599645187126799218473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3878396215329352524997045 363599645187126799218473)
                  ·
                    rfl

theorem cell22_3186485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_3186485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186485 prefixEnd_3186485 := by exact prefixLift 3186485
  have htrace : WordTrace (prefixWord ++ tailWord_3186485) baseStart_3186485 baseEnd_3186485 := by
    simpa [prefixWord, tailWord_3186485, baseEnd_3186485] using wordTrace_append hprefix tailTrace_3186485
  have hstable : (prefixWord ++ tailWord_3186485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186485).length < 2 ^ (prefixWord ++ tailWord_3186485).sum := by decide
  have hdescent : baseEnd_3186485 < baseStart_3186485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186502 : List Nat := [6, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_3186502 : Nat := 118140960795 + 3186502 * 2 ^ 59
def prefixEnd_3186502 : Nat := 4983230072969 + 3 ^ 40 * 3186502 * 2
def baseEnd_3186502 : Nat := 363601585002932673326789

theorem tailTrace_3186502 : CollatzResearch.WordTrace tailWord_3186502 prefixEnd_3186502 363601585002932673326789 := by
  unfold tailWord_3186502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3631914871932966876870055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77480850601236626706561173 3631914871932966876870055)
  ·
    refine ⟨5447872307899450315305083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3631914871932966876870055 5447872307899450315305083)
    ·
      refine ⟨8171808461849175472957625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5447872307899450315305083 8171808461849175472957625)
      ·
        refine ⟨6128856346386881604718219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8171808461849175472957625 6128856346386881604718219)
        ·
          refine ⟨9193284519580322407077329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6128856346386881604718219 9193284519580322407077329)
          ·
            refine ⟨6894963389685241805307997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9193284519580322407077329 6894963389685241805307997)
            ·
              refine ⟨2585611271131965676990499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6894963389685241805307997 2585611271131965676990499)
              ·
                refine ⟨3878416906697948515485749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585611271131965676990499 3878416906697948515485749)
                ·
                  refine ⟨363601585002932673326789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3878416906697948515485749 363601585002932673326789)
                  ·
                    rfl

theorem cell22_3186502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_3186502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186502 prefixEnd_3186502 := by exact prefixLift 3186502
  have htrace : WordTrace (prefixWord ++ tailWord_3186502) baseStart_3186502 baseEnd_3186502 := by
    simpa [prefixWord, tailWord_3186502, baseEnd_3186502] using wordTrace_append hprefix tailTrace_3186502
  have hstable : (prefixWord ++ tailWord_3186502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186502).length < 2 ^ (prefixWord ++ tailWord_3186502).sum := by decide
  have hdescent : baseEnd_3186502 < baseStart_3186502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186530 : List Nat := [3, 3, 2, 1, 2, 1, 3, 3, 4]
def baseStart_3186530 : Nat := 118140960795 + 3186530 * 2 ^ 59
def prefixEnd_3186530 : Nat := 4983230072969 + 3 ^ 40 * 3186530 * 2
def baseEnd_3186530 : Nat := 363604779993671760093427

theorem tailTrace_3186530 : CollatzResearch.WordTrace tailWord_3186530 prefixEnd_3186530 363604779993671760093427 := by
  unfold tailWord_3186530
  simp only [CollatzResearch.WordTrace]
  refine ⟨29055574286438375210465261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77481531430502333894574029 29055574286438375210465261)
  ·
    refine ⟨10895840357414390703924473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29055574286438375210465261 10895840357414390703924473)
    ·
      refine ⟨8171880268060793027943355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10895840357414390703924473 8171880268060793027943355)
      ·
        refine ⟨12257820402091189541915033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8171880268060793027943355 12257820402091189541915033)
        ·
          refine ⟨9193365301568392156436275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12257820402091189541915033 9193365301568392156436275)
          ·
            refine ⟨13790047952352588234654413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9193365301568392156436275 13790047952352588234654413)
            ·
              refine ⟨5171267982132220587995405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13790047952352588234654413 5171267982132220587995405)
              ·
                refine ⟨1939225493299582720498277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5171267982132220587995405 1939225493299582720498277)
                ·
                  refine ⟨363604779993671760093427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1939225493299582720498277 363604779993671760093427)
                  ·
                    rfl

theorem cell22_3186530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_3186530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186530 prefixEnd_3186530 := by exact prefixLift 3186530
  have htrace : WordTrace (prefixWord ++ tailWord_3186530) baseStart_3186530 baseEnd_3186530 := by
    simpa [prefixWord, tailWord_3186530, baseEnd_3186530] using wordTrace_append hprefix tailTrace_3186530
  have hstable : (prefixWord ++ tailWord_3186530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186530).length < 2 ^ (prefixWord ++ tailWord_3186530).sum := by decide
  have hdescent : baseEnd_3186530 < baseStart_3186530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186558 : List Nat := [4, 2, 3, 1, 1, 1, 1, 9]
def baseStart_3186558 : Nat := 118140960795 + 3186558 * 2 ^ 59
def prefixEnd_3186558 : Nat := 4983230072969 + 3 ^ 40 * 3186558 * 2
def baseEnd_3186558 : Nat := 121202658328136948953355

theorem tailTrace_3186558 : CollatzResearch.WordTrace tailWord_3186558 prefixEnd_3186558 121202658328136948953355 := by
  unfold tailWord_3186558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14527914798706507702985041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77482212259768041082586885 14527914798706507702985041)
  ·
    refine ⟨10895936099029880777238781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14527914798706507702985041 10895936099029880777238781)
    ·
      refine ⟨4085976037136205291464543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10895936099029880777238781 4085976037136205291464543)
      ·
        refine ⟨6128964055704307937196815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4085976037136205291464543 6128964055704307937196815)
        ·
          refine ⟨9193446083556461905795223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6128964055704307937196815 9193446083556461905795223)
          ·
            refine ⟨13790169125334692858692835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9193446083556461905795223 13790169125334692858692835)
            ·
              refine ⟨20685253688002039288039253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13790169125334692858692835 20685253688002039288039253)
              ·
                refine ⟨121202658328136948953355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20685253688002039288039253 121202658328136948953355)
                ·
                  rfl

theorem cell22_3186558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_3186558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186558 prefixEnd_3186558 := by exact prefixLift 3186558
  have htrace : WordTrace (prefixWord ++ tailWord_3186558) baseStart_3186558 baseEnd_3186558 := by
    simpa [prefixWord, tailWord_3186558, baseEnd_3186558] using wordTrace_append hprefix tailTrace_3186558
  have hstable : (prefixWord ++ tailWord_3186558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186558).length < 2 ^ (prefixWord ++ tailWord_3186558).sum := by decide
  have hdescent : baseEnd_3186558 < baseStart_3186558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186616 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 5, 4]
def baseStart_3186616 : Nat := 118140960795 + 3186616 * 2 ^ 59
def prefixEnd_3186616 : Nat := 4983230072969 + 3 ^ 40 * 3186616 * 2
def baseEnd_3186616 : Nat := 1090843779538539722630017

theorem tailTrace_3186616 : CollatzResearch.WordTrace tailWord_3186616 prefixEnd_3186616 1090843779538539722630017 := by
  unfold tailWord_3186616
  simp only [CollatzResearch.WordTrace]
  refine ⟨58112716911720968764745851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77483622548961291686327801 58112716911720968764745851)
  ·
    refine ⟨87169075367581453147118777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58112716911720968764745851 87169075367581453147118777)
    ·
      refine ⟨65376806525686089860339083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87169075367581453147118777 65376806525686089860339083)
      ·
        refine ⟨98065209788529134790508625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65376806525686089860339083 98065209788529134790508625)
        ·
          refine ⟨73548907341396851092881469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98065209788529134790508625 73548907341396851092881469)
          ·
            refine ⟨27580840253023819159830551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73548907341396851092881469 27580840253023819159830551)
            ·
              refine ⟨41371260379535728739745827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27580840253023819159830551 41371260379535728739745827)
              ·
                refine ⟨62056890569303593109618741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41371260379535728739745827 62056890569303593109618741)
                ·
                  refine ⟨5817833490872211854026757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62056890569303593109618741 5817833490872211854026757)
                  ·
                    refine ⟨1090843779538539722630017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5817833490872211854026757 1090843779538539722630017)
                    ·
                      rfl

theorem cell22_3186616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_3186616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186616 prefixEnd_3186616 := by exact prefixLift 3186616
  have htrace : WordTrace (prefixWord ++ tailWord_3186616) baseStart_3186616 baseEnd_3186616 := by
    simpa [prefixWord, tailWord_3186616, baseEnd_3186616] using wordTrace_append hprefix tailTrace_3186616
  have hstable : (prefixWord ++ tailWord_3186616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186616).length < 2 ^ (prefixWord ++ tailWord_3186616).sum := by decide
  have hdescent : baseEnd_3186616 < baseStart_3186616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186650 : List Nat := [3, 1, 1, 2, 5, 1, 1, 3, 1, 4]
def baseStart_3186650 : Nat := 118140960795 + 3186650 * 2 ^ 59
def prefixEnd_3186650 : Nat := 4983230072969 + 3 ^ 40 * 3186650 * 2
def baseEnd_3186650 : Nat := 1090855418433374967279913

theorem tailTrace_3186650 : CollatzResearch.WordTrace tailWord_3186650 prefixEnd_3186650 1090855418433374967279913 := by
  unfold tailWord_3186650
  simp only [CollatzResearch.WordTrace]
  refine ⟨29056668476329690334057351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77484449270212507557486269 29056668476329690334057351)
  ·
    refine ⟨43585002714494535501086027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29056668476329690334057351 43585002714494535501086027)
    ·
      refine ⟨65377504071741803251629041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43585002714494535501086027 65377504071741803251629041)
      ·
        refine ⟨49033128053806352438721781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65377504071741803251629041 49033128053806352438721781)
        ·
          refine ⟨4596855755044345541130167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49033128053806352438721781 4596855755044345541130167)
          ·
            refine ⟨6895283632566518311695251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4596855755044345541130167 6895283632566518311695251)
            ·
              refine ⟨10342925448849777467542877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6895283632566518311695251 10342925448849777467542877)
              ·
                refine ⟨3878597043318666550328579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10342925448849777467542877 3878597043318666550328579)
                ·
                  refine ⟨5817895564977999825492869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3878597043318666550328579 5817895564977999825492869)
                  ·
                    refine ⟨1090855418433374967279913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5817895564977999825492869 1090855418433374967279913)
                    ·
                      rfl

theorem cell22_3186650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_3186650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186650 prefixEnd_3186650 := by exact prefixLift 3186650
  have htrace : WordTrace (prefixWord ++ tailWord_3186650) baseStart_3186650 baseEnd_3186650 := by
    simpa [prefixWord, tailWord_3186650, baseEnd_3186650] using wordTrace_append hprefix tailTrace_3186650
  have hstable : (prefixWord ++ tailWord_3186650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186650).length < 2 ^ (prefixWord ++ tailWord_3186650).sum := by decide
  have hdescent : baseEnd_3186650 < baseStart_3186650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186693 : List Nat := [1, 3, 1, 1, 2, 4, 4, 6]
def baseStart_3186693 : Nat := 118140960795 + 3186693 * 2 ^ 59
def prefixEnd_3186693 : Nat := 4983230072969 + 3 ^ 40 * 3186693 * 2
def baseEnd_3186693 : Nat := 121207793134681909828309

theorem tailTrace_3186693 : CollatzResearch.WordTrace tailWord_3186693 prefixEnd_3186693 121207793134681909828309 := by
  unfold tailWord_3186693
  simp only [CollatzResearch.WordTrace]
  refine ⟨116228242244162979680044733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77485494829441986453363155 116228242244162979680044733)
  ·
    refine ⟨43585590841561117380016775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116228242244162979680044733 43585590841561117380016775)
    ·
      refine ⟨65378386262341676070025163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43585590841561117380016775 65378386262341676070025163)
      ·
        refine ⟨98067579393512514105037745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65378386262341676070025163 98067579393512514105037745)
        ·
          refine ⟨73550684545134385578778309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98067579393512514105037745 73550684545134385578778309)
          ·
            refine ⟨13790753352212697296020933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73550684545134385578778309 13790753352212697296020933)
            ·
              refine ⟨2585766253539880743003925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13790753352212697296020933 2585766253539880743003925)
              ·
                refine ⟨121207793134681909828309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2585766253539880743003925 121207793134681909828309)
                ·
                  rfl

theorem cell22_3186693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 6].length) (baseStart_3186693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186693 prefixEnd_3186693 := by exact prefixLift 3186693
  have htrace : WordTrace (prefixWord ++ tailWord_3186693) baseStart_3186693 baseEnd_3186693 := by
    simpa [prefixWord, tailWord_3186693, baseEnd_3186693] using wordTrace_append hprefix tailTrace_3186693
  have hstable : (prefixWord ++ tailWord_3186693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186693).length < 2 ^ (prefixWord ++ tailWord_3186693).sum := by decide
  have hdescent : baseEnd_3186693 < baseStart_3186693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186725 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 3, 3]
def baseStart_3186725 : Nat := 118140960795 + 3186725 * 2 ^ 59
def prefixEnd_3186725 : Nat := 4983230072969 + 3 ^ 40 * 3186725 * 2
def baseEnd_3186725 : Nat := 1090881092466099771654683

theorem tailTrace_3186725 : CollatzResearch.WordTrace tailWord_3186725 prefixEnd_3186725 1090881092466099771654683 := by
  unfold tailWord_3186725
  simp only [CollatzResearch.WordTrace]
  refine ⟨116229409380047049145209629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77486272920031366096806419 116229409380047049145209629)
  ·
    refine ⟨43586028517517643429453611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116229409380047049145209629 43586028517517643429453611)
    ·
      refine ⟨65379042776276465144180417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43586028517517643429453611 65379042776276465144180417)
      ·
        refine ⟨49034282082207348858135313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65379042776276465144180417 49034282082207348858135313)
        ·
          refine ⟨36775711561655511643601485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49034282082207348858135313 36775711561655511643601485)
          ·
            refine ⟨13790891835620816866350557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36775711561655511643601485 13790891835620816866350557)
            ·
              refine ⟨5171584438357806324881459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13790891835620816866350557 5171584438357806324881459)
              ·
                refine ⟨7757376657536709487322189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171584438357806324881459 7757376657536709487322189)
                ·
                  refine ⟨2909016246576266057745821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7757376657536709487322189 2909016246576266057745821)
                  ·
                    refine ⟨1090881092466099771654683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2909016246576266057745821 1090881092466099771654683)
                    ·
                      rfl

theorem cell22_3186725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_3186725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186725 prefixEnd_3186725 := by exact prefixLift 3186725
  have htrace : WordTrace (prefixWord ++ tailWord_3186725) baseStart_3186725 baseEnd_3186725 := by
    simpa [prefixWord, tailWord_3186725, baseEnd_3186725] using wordTrace_append hprefix tailTrace_3186725
  have hstable : (prefixWord ++ tailWord_3186725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186725).length < 2 ^ (prefixWord ++ tailWord_3186725).sum := by decide
  have hdescent : baseEnd_3186725 < baseStart_3186725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186849 : List Nat := [1, 2, 3, 3, 1, 3, 3, 1, 2, 3]
def baseStart_3186849 : Nat := 118140960795 + 3186849 * 2 ^ 59
def prefixEnd_3186849 : Nat := 4983230072969 + 3 ^ 40 * 3186849 * 2
def baseEnd_3186849 : Nat := 1090923540200204781554303

theorem tailTrace_3186849 : CollatzResearch.WordTrace tailWord_3186849 prefixEnd_3186849 1090923540200204781554303 := by
  unfold tailWord_3186849
  simp only [CollatzResearch.WordTrace]
  refine ⟨116233932031597818322723601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77489288021065212215149067 116233932031597818322723601)
  ·
    refine ⟨87175449023698363742042701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116233932031597818322723601 87175449023698363742042701)
    ·
      refine ⟨32690793383886886403266013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87175449023698363742042701 32690793383886886403266013)
      ·
        refine ⟨12259047518957582401224755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32690793383886886403266013 12259047518957582401224755)
        ·
          refine ⟨18388571278436373601837133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12259047518957582401224755 18388571278436373601837133)
          ·
            refine ⟨6895714229413640100688925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18388571278436373601837133 6895714229413640100688925)
            ·
              refine ⟨2585892836030115037758347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6895714229413640100688925 2585892836030115037758347)
              ·
                refine ⟨3878839254045172556637521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585892836030115037758347 3878839254045172556637521)
                ·
                  refine ⟨2909129440533879417478141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3878839254045172556637521 2909129440533879417478141)
                  ·
                    refine ⟨1090923540200204781554303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2909129440533879417478141 1090923540200204781554303)
                    ·
                      rfl

theorem cell22_3186849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_3186849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186849 prefixEnd_3186849 := by exact prefixLift 3186849
  have htrace : WordTrace (prefixWord ++ tailWord_3186849) baseStart_3186849 baseEnd_3186849 := by
    simpa [prefixWord, tailWord_3186849, baseEnd_3186849] using wordTrace_append hprefix tailTrace_3186849
  have hstable : (prefixWord ++ tailWord_3186849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186849).length < 2 ^ (prefixWord ++ tailWord_3186849).sum := by decide
  have hdescent : baseEnd_3186849 < baseStart_3186849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186873 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 9]
def baseStart_3186873 : Nat := 118140960795 + 3186873 * 2 ^ 59
def prefixEnd_3186873 : Nat := 4983230072969 + 3 ^ 40 * 3186873 * 2
def baseEnd_3186873 : Nat := 363643918630225572984743

theorem tailTrace_3186873 : CollatzResearch.WordTrace tailWord_3186873 prefixEnd_3186873 363643918630225572984743 := by
  unfold tailWord_3186873
  simp only [CollatzResearch.WordTrace]
  refine ⟨116234807383510870421597273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77489871589007246947731515 116234807383510870421597273)
  ·
    refine ⟨87176105537633152816197955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116234807383510870421597273 87176105537633152816197955)
    ·
      refine ⟨130764158306449729224296933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87176105537633152816197955 130764158306449729224296933)
      ·
        refine ⟨24518279682459324229555675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130764158306449729224296933 24518279682459324229555675)
        ·
          refine ⟨36777419523688986344333513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24518279682459324229555675 36777419523688986344333513)
          ·
            refine ⟨27583064642766739758250135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36777419523688986344333513 27583064642766739758250135)
            ·
              refine ⟨41374596964150109637375203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27583064642766739758250135 41374596964150109637375203)
              ·
                refine ⟨62061895446225164456062805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41374596964150109637375203 62061895446225164456062805)
                ·
                  refine ⟨363643918630225572984743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62061895446225164456062805 363643918630225572984743)
                  ·
                    rfl

theorem cell22_3186873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_3186873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186873 prefixEnd_3186873 := by exact prefixLift 3186873
  have htrace : WordTrace (prefixWord ++ tailWord_3186873) baseStart_3186873 baseEnd_3186873 := by
    simpa [prefixWord, tailWord_3186873, baseEnd_3186873] using wordTrace_append hprefix tailTrace_3186873
  have hstable : (prefixWord ++ tailWord_3186873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186873).length < 2 ^ (prefixWord ++ tailWord_3186873).sum := by decide
  have hdescent : baseEnd_3186873 < baseStart_3186873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186890 : List Nat := [3, 1, 2, 1, 3, 1, 2, 4, 5]
def baseStart_3186890 : Nat := 118140960795 + 3186890 * 2 ^ 59
def prefixEnd_3186890 : Nat := 4983230072969 + 3 ^ 40 * 3186890 * 2
def baseEnd_3186890 : Nat := 363645858446031447093059

theorem tailTrace_3186890 : CollatzResearch.WordTrace tailWord_3186890 prefixEnd_3186890 363645858446031447093059 := by
  unfold tailWord_3186890
  simp only [CollatzResearch.WordTrace]
  refine ⟨29058856856112320581241531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77490284949632854883310749 29058856856112320581241531)
  ·
    refine ⟨43588285284168480871862297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29058856856112320581241531 43588285284168480871862297)
    ·
      refine ⟨32691213963126360653896723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43588285284168480871862297 32691213963126360653896723)
      ·
        refine ⟨49036820944689540980845085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32691213963126360653896723 49036820944689540980845085)
        ·
          refine ⟨18388807854258577867816907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49036820944689540980845085 18388807854258577867816907)
          ·
            refine ⟨27583211781387866801725361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18388807854258577867816907 27583211781387866801725361)
            ·
              refine ⟨20687408836040900101294021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27583211781387866801725361 20687408836040900101294021)
              ·
                refine ⟨3878889156757668768992629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20687408836040900101294021 3878889156757668768992629)
                ·
                  refine ⟨363645858446031447093059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3878889156757668768992629 363645858446031447093059)
                  ·
                    rfl

theorem cell22_3186890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_3186890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186890 prefixEnd_3186890 := by exact prefixLift 3186890
  have htrace : WordTrace (prefixWord ++ tailWord_3186890) baseStart_3186890 baseEnd_3186890 := by
    simpa [prefixWord, tailWord_3186890, baseEnd_3186890] using wordTrace_append hprefix tailTrace_3186890
  have hstable : (prefixWord ++ tailWord_3186890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186890).length < 2 ^ (prefixWord ++ tailWord_3186890).sum := by decide
  have hdescent : baseEnd_3186890 < baseStart_3186890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186894 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_3186894 : Nat := 118140960795 + 3186894 * 2 ^ 59
def prefixEnd_3186894 : Nat := 4983230072969 + 3 ^ 40 * 3186894 * 2
def baseEnd_3186894 : Nat := 1090938944619839664179165

theorem tailTrace_3186894 : CollatzResearch.WordTrace tailWord_3186894 prefixEnd_3186894 1090938944619839664179165 := by
  unfold tailWord_3186894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14529446664554348876013967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77490382210956527338741157 14529446664554348876013967)
  ·
    refine ⟨21794169996831523314020951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14529446664554348876013967 21794169996831523314020951)
    ·
      refine ⟨32691254995247284971031427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21794169996831523314020951 32691254995247284971031427)
      ·
        refine ⟨49036882492870927456547141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32691254995247284971031427 49036882492870927456547141)
        ·
          refine ⟨9194415467413298898102589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49036882492870927456547141 9194415467413298898102589)
          ·
            refine ⟨3447905800279987086788471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9194415467413298898102589 3447905800279987086788471)
            ·
              refine ⟨5171858700419980630182707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447905800279987086788471 5171858700419980630182707)
              ·
                refine ⟨7757788050629970945274061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171858700419980630182707 7757788050629970945274061)
                ·
                  refine ⟨2909170518986239104477773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7757788050629970945274061 2909170518986239104477773)
                  ·
                    refine ⟨1090938944619839664179165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2909170518986239104477773 1090938944619839664179165)
                    ·
                      rfl

theorem cell22_3186894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_3186894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186894 prefixEnd_3186894 := by exact prefixLift 3186894
  have htrace : WordTrace (prefixWord ++ tailWord_3186894) baseStart_3186894 baseEnd_3186894 := by
    simpa [prefixWord, tailWord_3186894, baseEnd_3186894] using wordTrace_append hprefix tailTrace_3186894
  have hstable : (prefixWord ++ tailWord_3186894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186894).length < 2 ^ (prefixWord ++ tailWord_3186894).sum := by decide
  have hdescent : baseEnd_3186894 < baseStart_3186894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186903 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 2, 8]
def baseStart_3186903 : Nat := 118140960795 + 3186903 * 2 ^ 59
def prefixEnd_3186903 : Nat := 4983230072969 + 3 ^ 40 * 3186903 * 2
def baseEnd_3186903 : Nat := 1090942025503766640704137

theorem tailTrace_3186903 : CollatzResearch.WordTrace tailWord_3186903 prefixEnd_3186903 1090942025503766640704137 := by
  unfold tailWord_3186903
  simp only [CollatzResearch.WordTrace]
  refine ⟨116235901573402185545189363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77490601048934790363459575 116235901573402185545189363)
  ·
    refine ⟨174353852360103278317784045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116235901573402185545189363 174353852360103278317784045)
    ·
      refine ⟨65382694635038729369169017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174353852360103278317784045 65382694635038729369169017)
      ·
        refine ⟨49037020976279047026876763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65382694635038729369169017 49037020976279047026876763)
        ·
          refine ⟨73555531464418570540315145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49037020976279047026876763 73555531464418570540315145)
          ·
            refine ⟨55166648598313927905236359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73555531464418570540315145 55166648598313927905236359)
            ·
              refine ⟨82749972897470891857854539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55166648598313927905236359 82749972897470891857854539)
              ·
                refine ⟨124124959346206337786781809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82749972897470891857854539 124124959346206337786781809)
                ·
                  refine ⟨93093719509654753340086357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124124959346206337786781809 93093719509654753340086357)
                  ·
                    refine ⟨1090942025503766640704137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93093719509654753340086357 1090942025503766640704137)
                    ·
                      rfl

theorem cell22_3186903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_3186903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186903 prefixEnd_3186903 := by exact prefixLift 3186903
  have htrace : WordTrace (prefixWord ++ tailWord_3186903) baseStart_3186903 baseEnd_3186903 := by
    simpa [prefixWord, tailWord_3186903, baseEnd_3186903] using wordTrace_append hprefix tailTrace_3186903
  have hstable : (prefixWord ++ tailWord_3186903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186903).length < 2 ^ (prefixWord ++ tailWord_3186903).sum := by decide
  have hdescent : baseEnd_3186903 < baseStart_3186903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186965 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_3186965 : Nat := 118140960795 + 3186965 * 2 ^ 59
def prefixEnd_3186965 : Nat := 4983230072969 + 3 ^ 40 * 3186965 * 2
def baseEnd_3186965 : Nat := 1090963249370819145653947

theorem tailTrace_3186965 : CollatzResearch.WordTrace tailWord_3186965 prefixEnd_3186965 1090963249370819145653947 := by
  unfold tailWord_3186965
  simp only [CollatzResearch.WordTrace]
  refine ⟨116238162899177570133946349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77492108599451713422630899 116238162899177570133946349)
  ·
    refine ⟨43589311087191588800229881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116238162899177570133946349 43589311087191588800229881)
    ·
      refine ⟨32691983315393691600172411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43589311087191588800229881 32691983315393691600172411)
      ·
        refine ⟨49037974973090537400258617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32691983315393691600172411 49037974973090537400258617)
        ·
          refine ⟨36778481229817903050193963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49037974973090537400258617 36778481229817903050193963)
          ·
            refine ⟨55167721844726854575290945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36778481229817903050193963 55167721844726854575290945)
            ·
              refine ⟨41375791383545140931468209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55167721844726854575290945 41375791383545140931468209)
              ·
                refine ⟨31031843537658855698601157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41375791383545140931468209 31031843537658855698601157)
                ·
                  refine ⟨5818470663311035443487717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31031843537658855698601157 5818470663311035443487717)
                  ·
                    refine ⟨1090963249370819145653947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5818470663311035443487717 1090963249370819145653947)
                    ·
                      rfl

theorem cell22_3186965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_3186965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186965 prefixEnd_3186965 := by exact prefixLift 3186965
  have htrace : WordTrace (prefixWord ++ tailWord_3186965) baseStart_3186965 baseEnd_3186965 := by
    simpa [prefixWord, tailWord_3186965, baseEnd_3186965] using wordTrace_append hprefix tailTrace_3186965
  have hstable : (prefixWord ++ tailWord_3186965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186965).length < 2 ^ (prefixWord ++ tailWord_3186965).sum := by decide
  have hdescent : baseEnd_3186965 < baseStart_3186965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186967 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 1, 5]
def baseStart_3186967 : Nat := 118140960795 + 3186967 * 2 ^ 59
def prefixEnd_3186967 : Nat := 4983230072969 + 3 ^ 40 * 3186967 * 2
def baseEnd_3186967 : Nat := 1090963934011691807103941

theorem tailTrace_3186967 : CollatzResearch.WordTrace tailWord_3186967 prefixEnd_3186967 1090963934011691807103941 := by
  unfold tailWord_3186967
  simp only [CollatzResearch.WordTrace]
  refine ⟨116238235845170324475519155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77492157230113549650346103 116238235845170324475519155)
  ·
    refine ⟨174357353767755486713278733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116238235845170324475519155 174357353767755486713278733)
    ·
      refine ⟨65384007662908307517479525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174357353767755486713278733 65384007662908307517479525)
      ·
        refine ⟨12259501436795307659527411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65384007662908307517479525 12259501436795307659527411)
        ·
          refine ⟨18389252155192961489291117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12259501436795307659527411 18389252155192961489291117)
          ·
            refine ⟨6895969558197360558484169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18389252155192961489291117 6895969558197360558484169)
            ·
              refine ⟨5171977168648020418863127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6895969558197360558484169 5171977168648020418863127)
              ·
                refine ⟨7757965752972030628294691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171977168648020418863127 7757965752972030628294691)
                ·
                  refine ⟨11636948629458045942442037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7757965752972030628294691 11636948629458045942442037)
                  ·
                    refine ⟨1090963934011691807103941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11636948629458045942442037 1090963934011691807103941)
                    ·
                      rfl

theorem cell22_3186967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_3186967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186967 prefixEnd_3186967 := by exact prefixLift 3186967
  have htrace : WordTrace (prefixWord ++ tailWord_3186967) baseStart_3186967 baseEnd_3186967 := by
    simpa [prefixWord, tailWord_3186967, baseEnd_3186967] using wordTrace_append hprefix tailTrace_3186967
  have hstable : (prefixWord ++ tailWord_3186967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186967).length < 2 ^ (prefixWord ++ tailWord_3186967).sum := by decide
  have hdescent : baseEnd_3186967 < baseStart_3186967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186986 : List Nat := [3, 1, 4, 2, 2, 1, 2, 3, 4]
def baseStart_3186986 : Nat := 118140960795 + 3186986 * 2 ^ 59
def prefixEnd_3186986 : Nat := 4983230072969 + 3 ^ 40 * 3186986 * 2
def baseEnd_3186986 : Nat := 363656812699994030292961

theorem tailTrace_3186986 : CollatzResearch.WordTrace tailWord_3186986 prefixEnd_3186986 363656812699994030292961 := by
  unfold tailWord_3186986
  simp only [CollatzResearch.WordTrace]
  refine ⟨29059732208025372680115203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77492619221400993813640541 29059732208025372680115203)
  ·
    refine ⟨43589598312038059020172805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29059732208025372680115203 43589598312038059020172805)
    ·
      refine ⟨8173049683507136066282401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43589598312038059020172805 8173049683507136066282401)
      ·
        refine ⟨6129787262630352049711801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8173049683507136066282401 6129787262630352049711801)
        ·
          refine ⟨4597340446972764037283851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6129787262630352049711801 4597340446972764037283851)
          ·
            refine ⟨6896010670459146055925777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4597340446972764037283851 6896010670459146055925777)
            ·
              refine ⟨5172008002844359541944333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6896010670459146055925777 5172008002844359541944333)
              ·
                refine ⟨1939503001066634828229125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5172008002844359541944333 1939503001066634828229125)
                ·
                  refine ⟨363656812699994030292961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1939503001066634828229125 363656812699994030292961)
                  ·
                    rfl

theorem cell22_3186986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_3186986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3186986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3186986 prefixEnd_3186986 := by exact prefixLift 3186986
  have htrace : WordTrace (prefixWord ++ tailWord_3186986) baseStart_3186986 baseEnd_3186986 := by
    simpa [prefixWord, tailWord_3186986, baseEnd_3186986] using wordTrace_append hprefix tailTrace_3186986
  have hstable : (prefixWord ++ tailWord_3186986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186986).length < 2 ^ (prefixWord ++ tailWord_3186986).sum := by decide
  have hdescent : baseEnd_3186986 < baseStart_3186986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187001 : List Nat := [1, 2, 1, 6, 1, 3, 1, 2, 2, 3]
def baseStart_3187001 : Nat := 118140960795 + 3187001 * 2 ^ 59
def prefixEnd_3187001 : Nat := 4983230072969 + 3 ^ 40 * 3187001 * 2
def baseEnd_3187001 : Nat := 1090975572906527051753837

theorem tailTrace_3187001 : CollatzResearch.WordTrace tailWord_3187001 prefixEnd_3187001 1090975572906527051753837 := by
  unfold tailWord_3187001
  simp only [CollatzResearch.WordTrace]
  refine ⟨116239475927047148282256857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77492983951364765521504571 116239475927047148282256857)
  ·
    refine ⟨87179606945285361211692643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116239475927047148282256857 87179606945285361211692643)
    ·
      refine ⟨130769410417928041817538965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87179606945285361211692643 130769410417928041817538965)
      ·
        refine ⟨6129816113340376960197139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130769410417928041817538965 6129816113340376960197139)
        ·
          refine ⟨9194724170010565440295709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6129816113340376960197139 9194724170010565440295709)
          ·
            refine ⟨3448021563753962040110891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9194724170010565440295709 3448021563753962040110891)
            ·
              refine ⟨5172032345630943060166337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448021563753962040110891 5172032345630943060166337)
              ·
                refine ⟨3879024259223207295124753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5172032345630943060166337 3879024259223207295124753)
                ·
                  refine ⟨2909268194417405471343565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3879024259223207295124753 2909268194417405471343565)
                  ·
                    refine ⟨1090975572906527051753837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2909268194417405471343565 1090975572906527051753837)
                    ·
                      rfl

theorem cell22_3187001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 3].length) (baseStart_3187001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187001 prefixEnd_3187001 := by exact prefixLift 3187001
  have htrace : WordTrace (prefixWord ++ tailWord_3187001) baseStart_3187001 baseEnd_3187001 := by
    simpa [prefixWord, tailWord_3187001, baseEnd_3187001] using wordTrace_append hprefix tailTrace_3187001
  have hstable : (prefixWord ++ tailWord_3187001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187001).length < 2 ^ (prefixWord ++ tailWord_3187001).sum := by decide
  have hdescent : baseEnd_3187001 < baseStart_3187001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187042 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 7]
def baseStart_3187042 : Nat := 118140960795 + 3187042 * 2 ^ 59
def prefixEnd_3187042 : Nat := 4983230072969 + 3 ^ 40 * 3187042 * 2
def baseEnd_3187042 : Nat := 363663202681472203826237

theorem tailTrace_3187042 : CollatzResearch.WordTrace tailWord_3187042 prefixEnd_3187042 363663202681472203826237 := by
  unfold tailWord_3187042
  simp only [CollatzResearch.WordTrace]
  refine ⟨29060242829974653071124845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77493980879932408189666253 29060242829974653071124845)
  ·
    refine ⟨10897591061240494901671817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29060242829974653071124845 10897591061240494901671817)
    ·
      refine ⟨8173193295930371176253863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10897591061240494901671817 8173193295930371176253863)
      ·
        refine ⟨12259789943895556764380795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8173193295930371176253863 12259789943895556764380795)
        ·
          refine ⟨18389684915843335146571193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12259789943895556764380795 18389684915843335146571193)
          ·
            refine ⟨13792263686882501359928395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18389684915843335146571193 13792263686882501359928395)
            ·
              refine ⟨20688395530323752039892593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13792263686882501359928395 20688395530323752039892593)
              ·
                refine ⟨15516296647742814029919445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20688395530323752039892593 15516296647742814029919445)
                ·
                  refine ⟨363663202681472203826237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15516296647742814029919445 363663202681472203826237)
                  ·
                    rfl

theorem cell22_3187042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_3187042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187042 prefixEnd_3187042 := by exact prefixLift 3187042
  have htrace : WordTrace (prefixWord ++ tailWord_3187042) baseStart_3187042 baseEnd_3187042 := by
    simpa [prefixWord, tailWord_3187042, baseEnd_3187042] using wordTrace_append hprefix tailTrace_3187042
  have hstable : (prefixWord ++ tailWord_3187042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187042).length < 2 ^ (prefixWord ++ tailWord_3187042).sum := by decide
  have hdescent : baseEnd_3187042 < baseStart_3187042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187106 : List Nat := [3, 3, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_3187106 : Nat := 118140960795 + 3187106 * 2 ^ 59
def prefixEnd_3187106 : Nat := 4983230072969 + 3 ^ 40 * 3187106 * 2
def baseEnd_3187106 : Nat := 1091011516552341777878515

theorem tailTrace_3187106 : CollatzResearch.WordTrace tailWord_3187106 prefixEnd_3187106 1091011516552341777878515 := by
  unfold tailWord_3187106
  simp only [CollatzResearch.WordTrace]
  refine ⟨29060826397916687803707293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77495537061111167476552781 29060826397916687803707293)
  ·
    refine ⟨10897809899218757926390235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29060826397916687803707293 10897809899218757926390235)
    ·
      refine ⟨16346714848828136889585353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10897809899218757926390235 16346714848828136889585353)
      ·
        refine ⟨12260036136621102667189015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16346714848828136889585353 12260036136621102667189015)
        ·
          refine ⟨18390054204931654000783523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12260036136621102667189015 18390054204931654000783523)
          ·
            refine ⟨27585081307397481001175285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18390054204931654000783523 27585081307397481001175285)
            ·
              refine ⟨2586101372568513843860183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27585081307397481001175285 2586101372568513843860183)
              ·
                refine ⟨3879152058852770765790275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2586101372568513843860183 3879152058852770765790275)
                ·
                  refine ⟨5818728088279156148685413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3879152058852770765790275 5818728088279156148685413)
                  ·
                    refine ⟨1091011516552341777878515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5818728088279156148685413 1091011516552341777878515)
                    ·
                      rfl

theorem cell22_3187106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_3187106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187106 prefixEnd_3187106 := by exact prefixLift 3187106
  have htrace : WordTrace (prefixWord ++ tailWord_3187106) baseStart_3187106 baseEnd_3187106 := by
    simpa [prefixWord, tailWord_3187106, baseEnd_3187106] using wordTrace_append hprefix tailTrace_3187106
  have hstable : (prefixWord ++ tailWord_3187106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187106).length < 2 ^ (prefixWord ++ tailWord_3187106).sum := by decide
  have hdescent : baseEnd_3187106 < baseStart_3187106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187114 : List Nat := [3, 1, 6, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3187114 : Nat := 118140960795 + 3187114 * 2 ^ 59
def prefixEnd_3187114 : Nat := 4983230072969 + 3 ^ 40 * 3187114 * 2
def baseEnd_3187114 : Nat := 1091014255115832423678491

theorem tailTrace_3187114 : CollatzResearch.WordTrace tailWord_3187114 prefixEnd_3187114 1091014255115832423678491 := by
  unfold tailWord_3187114
  simp only [CollatzResearch.WordTrace]
  refine ⟨29060899343909442145280099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77495731583758512387413597 29060899343909442145280099)
  ·
    refine ⟨43591349015864163217920149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29060899343909442145280099 43591349015864163217920149)
    ·
      refine ⟨2043344485118632650840007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43591349015864163217920149 2043344485118632650840007)
      ·
        refine ⟨3065016727677948976260011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2043344485118632650840007 3065016727677948976260011)
        ·
          refine ⟨4597525091516923464390017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3065016727677948976260011 4597525091516923464390017)
          ·
            refine ⟨3448143818637692598292513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4597525091516923464390017 3448143818637692598292513)
            ·
              refine ⟨2586107863978269448719385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3448143818637692598292513 2586107863978269448719385)
              ·
                refine ⟨1939580897983702086539539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2586107863978269448719385 1939580897983702086539539)
                ·
                  refine ⟨2909371346975553129809309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939580897983702086539539 2909371346975553129809309)
                  ·
                    refine ⟨1091014255115832423678491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2909371346975553129809309 1091014255115832423678491)
                    ·
                      rfl

theorem cell22_3187114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3187114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187114 prefixEnd_3187114 := by exact prefixLift 3187114
  have htrace : WordTrace (prefixWord ++ tailWord_3187114) baseStart_3187114 baseEnd_3187114 := by
    simpa [prefixWord, tailWord_3187114, baseEnd_3187114] using wordTrace_append hprefix tailTrace_3187114
  have hstable : (prefixWord ++ tailWord_3187114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187114).length < 2 ^ (prefixWord ++ tailWord_3187114).sum := by decide
  have hdescent : baseEnd_3187114 < baseStart_3187114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187121 : List Nat := [1, 2, 2, 4, 1, 2, 4, 2, 4]
def baseStart_3187121 : Nat := 118140960795 + 3187121 * 2 ^ 59
def prefixEnd_3187121 : Nat := 4983230072969 + 3 ^ 40 * 3187121 * 2
def baseEnd_3187121 : Nat := 363672217119628912917823

theorem tailTrace_3187121 : CollatzResearch.WordTrace tailWord_3187121 prefixEnd_3187121 363672217119628912917823 := by
  unfold tailWord_3187121
  simp only [CollatzResearch.WordTrace]
  refine ⟨116243852686612408776625217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77495901791074939184416811 116243852686612408776625217)
  ·
    refine ⟨87182889514959306582468913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116243852686612408776625217 87182889514959306582468913)
    ·
      refine ⟨65387167136219479936851685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87182889514959306582468913 65387167136219479936851685)
      ·
        refine ⟨12260093838041152488159691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65387167136219479936851685 12260093838041152488159691)
        ·
          refine ⟨18390140757061728732239537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12260093838041152488159691 18390140757061728732239537)
          ·
            refine ⟨13792605567796296549179653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18390140757061728732239537 13792605567796296549179653)
            ·
              refine ⟨2586113543961805602971185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13792605567796296549179653 2586113543961805602971185)
              ·
                refine ⟨1939585157971354202228389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2586113543961805602971185 1939585157971354202228389)
                ·
                  refine ⟨363672217119628912917823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1939585157971354202228389 363672217119628912917823)
                  ·
                    rfl

theorem cell22_3187121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 4].length) (baseStart_3187121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187121 prefixEnd_3187121 := by exact prefixLift 3187121
  have htrace : WordTrace (prefixWord ++ tailWord_3187121) baseStart_3187121 baseEnd_3187121 := by
    simpa [prefixWord, tailWord_3187121, baseEnd_3187121] using wordTrace_append hprefix tailTrace_3187121
  have hstable : (prefixWord ++ tailWord_3187121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187121).length < 2 ^ (prefixWord ++ tailWord_3187121).sum := by decide
  have hdescent : baseEnd_3187121 < baseStart_3187121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187177 : List Nat := [1, 2, 1, 1, 1, 2, 1, 8, 5]
def baseStart_3187177 : Nat := 118140960795 + 3187177 * 2 ^ 59
def prefixEnd_3187177 : Nat := 4983230072969 + 3 ^ 40 * 3187177 * 2
def baseEnd_3187177 : Nat := 363678607101107086451099

theorem tailTrace_3187177 : CollatzResearch.WordTrace tailWord_3187177 prefixEnd_3187177 363678607101107086451099 := by
  unfold tailWord_3187177
  simp only [CollatzResearch.WordTrace]
  refine ⟨116245895174409530340663785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77497263449606353560442523 116245895174409530340663785)
  ·
    refine ⟨87184421380807147755497839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116245895174409530340663785 87184421380807147755497839)
    ·
      refine ⟨130776632071210721633246759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87184421380807147755497839 130776632071210721633246759)
      ·
        refine ⟨196164948106816082449870139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130776632071210721633246759 196164948106816082449870139)
        ·
          refine ⟨294247422160224123674805209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196164948106816082449870139 294247422160224123674805209)
          ·
            refine ⟨220685566620168092756103907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294247422160224123674805209 220685566620168092756103907)
            ·
              refine ⟨331028349930252139134155861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220685566620168092756103907 331028349930252139134155861)
              ·
                refine ⟨3879238475745142255478389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 331028349930252139134155861 3879238475745142255478389)
                ·
                  refine ⟨363678607101107086451099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3879238475745142255478389 363678607101107086451099)
                  ·
                    rfl

theorem cell22_3187177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 5].length) (baseStart_3187177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187177 prefixEnd_3187177 := by exact prefixLift 3187177
  have htrace : WordTrace (prefixWord ++ tailWord_3187177) baseStart_3187177 baseEnd_3187177 := by
    simpa [prefixWord, tailWord_3187177, baseEnd_3187177] using wordTrace_append hprefix tailTrace_3187177
  have hstable : (prefixWord ++ tailWord_3187177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187177).length < 2 ^ (prefixWord ++ tailWord_3187177).sum := by decide
  have hdescent : baseEnd_3187177 < baseStart_3187177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187181 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_3187181 : Nat := 118140960795 + 3187181 * 2 ^ 59
def prefixEnd_3187181 : Nat := 4983230072969 + 3 ^ 40 * 3187181 * 2
def baseEnd_3187181 : Nat := 1091037190585066582253285

theorem tailTrace_3187181 : CollatzResearch.WordTrace tailWord_3187181 prefixEnd_3187181 1091037190585066582253285 := by
  unfold tailWord_3187181
  simp only [CollatzResearch.WordTrace]
  refine ⟨116246041066395039023809397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77497360710930026015872931 116246041066395039023809397)
  ·
    refine ⟨10898066349974534908482131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116246041066395039023809397 10898066349974534908482131)
    ·
      refine ⟨16347099524961802362723197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10898066349974534908482131 16347099524961802362723197)
      ·
        refine ⟨6130162321860675886021199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16347099524961802362723197 6130162321860675886021199)
        ·
          refine ⟨9195243482791013829031799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6130162321860675886021199 9195243482791013829031799)
          ·
            refine ⟨13792865224186520743547699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9195243482791013829031799 13792865224186520743547699)
            ·
              refine ⟨20689297836279781115321549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13792865224186520743547699 20689297836279781115321549)
              ·
                refine ⟨7758486688604917918245581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20689297836279781115321549 7758486688604917918245581)
                ·
                  refine ⟨2909432508226844219342093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7758486688604917918245581 2909432508226844219342093)
                  ·
                    refine ⟨1091037190585066582253285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2909432508226844219342093 1091037190585066582253285)
                    ·
                      rfl

theorem cell22_3187181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_3187181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187181 prefixEnd_3187181 := by exact prefixLift 3187181
  have htrace : WordTrace (prefixWord ++ tailWord_3187181) baseStart_3187181 baseEnd_3187181 := by
    simpa [prefixWord, tailWord_3187181, baseEnd_3187181] using wordTrace_append hprefix tailTrace_3187181
  have hstable : (prefixWord ++ tailWord_3187181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187181).length < 2 ^ (prefixWord ++ tailWord_3187181).sum := by decide
  have hdescent : baseEnd_3187181 < baseStart_3187181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187192 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 2, 5]
def baseStart_3187192 : Nat := 118140960795 + 3187192 * 2 ^ 59
def prefixEnd_3187192 : Nat := 4983230072969 + 3 ^ 40 * 3187192 * 2
def baseEnd_3187192 : Nat := 1091040956109866220228251

theorem tailTrace_3187192 : CollatzResearch.WordTrace tailWord_3187192 prefixEnd_3187192 1091040956109866220228251 := by
  unfold tailWord_3187192
  simp only [CollatzResearch.WordTrace]
  refine ⟨58123221134677593951229915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77497628179570125268306553 58123221134677593951229915)
  ·
    refine ⟨87184831702016390926844873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58123221134677593951229915 87184831702016390926844873)
    ·
      refine ⟨65388623776512293195133655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87184831702016390926844873 65388623776512293195133655)
      ·
        refine ⟨98082935664768439792700483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65388623776512293195133655 98082935664768439792700483)
        ·
          refine ⟨147124403497152659689050725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98082935664768439792700483 147124403497152659689050725)
          ·
            refine ⟨27585825655716123691697011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147124403497152659689050725 27585825655716123691697011)
            ·
              refine ⟨41378738483574185537545517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27585825655716123691697011 41378738483574185537545517)
              ·
                refine ⟨15517026931340319576579569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41378738483574185537545517 15517026931340319576579569)
                ·
                  refine ⟨11637770198505239682434677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15517026931340319576579569 11637770198505239682434677)
                  ·
                    refine ⟨1091040956109866220228251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11637770198505239682434677 1091040956109866220228251)
                    ·
                      rfl

theorem cell22_3187192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_3187192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187192 prefixEnd_3187192 := by exact prefixLift 3187192
  have htrace : WordTrace (prefixWord ++ tailWord_3187192) baseStart_3187192 baseEnd_3187192 := by
    simpa [prefixWord, tailWord_3187192, baseEnd_3187192] using wordTrace_append hprefix tailTrace_3187192
  have hstable : (prefixWord ++ tailWord_3187192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187192).length < 2 ^ (prefixWord ++ tailWord_3187192).sum := by decide
  have hdescent : baseEnd_3187192 < baseStart_3187192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187245 : List Nat := [1, 5, 4, 1, 1, 1, 1, 3, 5]
def baseStart_3187245 : Nat := 118140960795 + 3187245 * 2 ^ 59
def prefixEnd_3187245 : Nat := 4983230072969 + 3 ^ 40 * 3187245 * 2
def baseEnd_3187245 : Nat := 363686366364330582884363

theorem tailTrace_3187245 : CollatzResearch.WordTrace tailWord_3187245 prefixEnd_3187245 363686366364330582884363 := by
  unfold tailWord_3187245
  simp only [CollatzResearch.WordTrace]
  refine ⟨116248375338163177954139189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77498916892108785302759459 116248375338163177954139189)
  ·
    refine ⟨10898285187952797933200549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116248375338163177954139189 10898285187952797933200549)
    ·
      refine ⟨2043428472741149612475103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10898285187952797933200549 2043428472741149612475103)
      ·
        refine ⟨3065142709111724418712655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2043428472741149612475103 3065142709111724418712655)
        ·
          refine ⟨4597714063667586628068983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3065142709111724418712655 4597714063667586628068983)
          ·
            refine ⟨6896571095501379942103475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4597714063667586628068983 6896571095501379942103475)
            ·
              refine ⟨10344856643252069913155213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6896571095501379942103475 10344856643252069913155213)
              ·
                refine ⟨3879321241219526217433205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10344856643252069913155213 3879321241219526217433205)
                ·
                  refine ⟨363686366364330582884363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3879321241219526217433205 363686366364330582884363)
                  ·
                    rfl

theorem cell22_3187245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_3187245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187245 prefixEnd_3187245 := by exact prefixLift 3187245
  have htrace : WordTrace (prefixWord ++ tailWord_3187245) baseStart_3187245 baseEnd_3187245 := by
    simpa [prefixWord, tailWord_3187245, baseEnd_3187245] using wordTrace_append hprefix tailTrace_3187245
  have hstable : (prefixWord ++ tailWord_3187245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187245).length < 2 ^ (prefixWord ++ tailWord_3187245).sum := by decide
  have hdescent : baseEnd_3187245 < baseStart_3187245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187269 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_3187269 : Nat := 118140960795 + 3187269 * 2 ^ 59
def prefixEnd_3187269 : Nat := 4983230072969 + 3 ^ 40 * 3187269 * 2
def baseEnd_3187269 : Nat := 1091067314783463686053015

theorem tailTrace_3187269 : CollatzResearch.WordTrace tailWord_3187269 prefixEnd_3187269 1091067314783463686053015 := by
  unfold tailWord_3187269
  simp only [CollatzResearch.WordTrace]
  refine ⟨116249250690076230053012861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77499500460050820035341907 116249250690076230053012861)
  ·
    refine ⟨43593469008778586269879823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116249250690076230053012861 43593469008778586269879823)
    ·
      refine ⟨65390203513167879404819735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43593469008778586269879823 65390203513167879404819735)
      ·
        refine ⟨98085305269751819107229603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65390203513167879404819735 98085305269751819107229603)
        ·
          refine ⟨147127957904627728660844405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98085305269751819107229603 147127957904627728660844405)
          ·
            refine ⟨13793246053558849561954163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147127957904627728660844405 13793246053558849561954163)
            ·
              refine ⟨20689869080338274342931245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13793246053558849561954163 20689869080338274342931245)
              ·
                refine ⟨7758700905126852878599217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20689869080338274342931245 7758700905126852878599217)
                ·
                  refine ⟨5819025678845139658949413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7758700905126852878599217 5819025678845139658949413)
                  ·
                    refine ⟨1091067314783463686053015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5819025678845139658949413 1091067314783463686053015)
                    ·
                      rfl

theorem cell22_3187269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_3187269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187269 prefixEnd_3187269 := by exact prefixLift 3187269
  have htrace : WordTrace (prefixWord ++ tailWord_3187269) baseStart_3187269 baseEnd_3187269 := by
    simpa [prefixWord, tailWord_3187269, baseEnd_3187269] using wordTrace_append hprefix tailTrace_3187269
  have hstable : (prefixWord ++ tailWord_3187269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187269).length < 2 ^ (prefixWord ++ tailWord_3187269).sum := by decide
  have hdescent : baseEnd_3187269 < baseStart_3187269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187301 : List Nat := [1, 3, 1, 3, 4, 2, 1, 7]
def baseStart_3187301 : Nat := 118140960795 + 3187301 * 2 ^ 59
def prefixEnd_3187301 : Nat := 4983230072969 + 3 ^ 40 * 3187301 * 2
def baseEnd_3187301 : Nat := 121230918781936252139213

theorem tailTrace_3187301 : CollatzResearch.WordTrace tailWord_3187301 prefixEnd_3187301 121230918781936252139213 := by
  unfold tailWord_3187301
  simp only [CollatzResearch.WordTrace]
  refine ⟨116250417825960299518177757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77500278550640199678785171 116250417825960299518177757)
  ·
    refine ⟨43593906684735112319316659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116250417825960299518177757 43593906684735112319316659)
    ·
      refine ⟨65390860027102668478974989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43593906684735112319316659 65390860027102668478974989)
      ·
        refine ⟨24521572510163500679615621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65390860027102668478974989 24521572510163500679615621)
        ·
          refine ⟨4597794845655656377427929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24521572510163500679615621 4597794845655656377427929)
          ·
            refine ⟨3448346134241742283070947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4597794845655656377427929 3448346134241742283070947)
            ·
              refine ⟨5172519201362613424606421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448346134241742283070947 5172519201362613424606421)
              ·
                refine ⟨121230918781936252139213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5172519201362613424606421 121230918781936252139213)
                ·
                  rfl

theorem cell22_3187301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 7].length) (baseStart_3187301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187301 prefixEnd_3187301 := by exact prefixLift 3187301
  have htrace : WordTrace (prefixWord ++ tailWord_3187301) baseStart_3187301 baseEnd_3187301 := by
    simpa [prefixWord, tailWord_3187301, baseEnd_3187301] using wordTrace_append hprefix tailTrace_3187301
  have hstable : (prefixWord ++ tailWord_3187301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187301).length < 2 ^ (prefixWord ++ tailWord_3187301).sum := by decide
  have hdescent : baseEnd_3187301 < baseStart_3187301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187318 : List Nat := [5, 1, 1, 2, 3, 1, 3, 6]
def baseStart_3187318 : Nat := 118140960795 + 3187318 * 2 ^ 59
def prefixEnd_3187318 : Nat := 4983230072969 + 3 ^ 40 * 3187318 * 2
def baseEnd_3187318 : Nat := 121231565387204876841985

theorem tailTrace_3187318 : CollatzResearch.WordTrace tailWord_3187318 prefixEnd_3187318 121231565387204876841985 := by
  unfold tailWord_3187318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7265689866681169463846663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77500691911265807614364405 7265689866681169463846663)
  ·
    refine ⟨10898534800021754195769995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7265689866681169463846663 10898534800021754195769995)
    ·
      refine ⟨16347802200032631293654993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10898534800021754195769995 16347802200032631293654993)
      ·
        refine ⟨12260851650024473470241245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16347802200032631293654993 12260851650024473470241245)
        ·
          refine ⟨4597819368759177551340467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12260851650024473470241245 4597819368759177551340467)
          ·
            refine ⟨6896729053138766327010701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4597819368759177551340467 6896729053138766327010701)
            ·
              refine ⟨2586273394927037372629013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6896729053138766327010701 2586273394927037372629013)
              ·
                refine ⟨121231565387204876841985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2586273394927037372629013 121231565387204876841985)
                ·
                  rfl

theorem cell22_3187318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_3187318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187318 prefixEnd_3187318 := by exact prefixLift 3187318
  have htrace : WordTrace (prefixWord ++ tailWord_3187318) baseStart_3187318 baseEnd_3187318 := by
    simpa [prefixWord, tailWord_3187318, baseEnd_3187318] using wordTrace_append hprefix tailTrace_3187318
  have hstable : (prefixWord ++ tailWord_3187318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187318).length < 2 ^ (prefixWord ++ tailWord_3187318).sum := by decide
  have hdescent : baseEnd_3187318 < baseStart_3187318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187329 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 7]
def baseStart_3187329 : Nat := 118140960795 + 3187329 * 2 ^ 59
def prefixEnd_3187329 : Nat := 4983230072969 + 3 ^ 40 * 3187329 * 2
def baseEnd_3187329 : Nat := 363695951336547843184277

theorem tailTrace_3187329 : CollatzResearch.WordTrace tailWord_3187329 prefixEnd_3187329 363695951336547843184277 := by
  unfold tailWord_3187329
  simp only [CollatzResearch.WordTrace]
  refine ⟨116251439069858860300197041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77500959379905906866798027 116251439069858860300197041)
  ·
    refine ⟨87188579302394145225147781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116251439069858860300197041 87188579302394145225147781)
    ·
      refine ⟨16347858619198902229715209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87188579302394145225147781 16347858619198902229715209)
      ·
        refine ⟨12260893964399176672286407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16347858619198902229715209 12260893964399176672286407)
        ·
          refine ⟨18391340946598765008429611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12260893964399176672286407 18391340946598765008429611)
          ·
            refine ⟨27587011419898147512644417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18391340946598765008429611 27587011419898147512644417)
            ·
              refine ⟨20690258564923610634483313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27587011419898147512644417 20690258564923610634483313)
              ·
                refine ⟨15517693923692707975862485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20690258564923610634483313 15517693923692707975862485)
                ·
                  refine ⟨363695951336547843184277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15517693923692707975862485 363695951336547843184277)
                  ·
                    rfl

theorem cell22_3187329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_3187329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187329 prefixEnd_3187329 := by exact prefixLift 3187329
  have htrace : WordTrace (prefixWord ++ tailWord_3187329) baseStart_3187329 baseEnd_3187329 := by
    simpa [prefixWord, tailWord_3187329, baseEnd_3187329] using wordTrace_append hprefix tailTrace_3187329
  have hstable : (prefixWord ++ tailWord_3187329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187329).length < 2 ^ (prefixWord ++ tailWord_3187329).sum := by decide
  have hdescent : baseEnd_3187329 < baseStart_3187329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187333 : List Nat := [1, 3, 1, 1, 4, 2, 1, 5, 1, 3]
def baseStart_3187333 : Nat := 118140960795 + 3187333 * 2 ^ 59
def prefixEnd_3187333 : Nat := 4983230072969 + 3 ^ 40 * 3187333 * 2
def baseEnd_3187333 : Nat := 1091089223291388852452819

theorem tailTrace_3187333 : CollatzResearch.WordTrace tailWord_3187333 prefixEnd_3187333 1091089223291388852452819 := by
  unfold tailWord_3187333
  simp only [CollatzResearch.WordTrace]
  refine ⟨116251584961844368983342653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77501056641229579322228435 116251584961844368983342653)
  ·
    refine ⟨43594344360691638368753495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116251584961844368983342653 43594344360691638368753495)
    ·
      refine ⟨65391516541037457553130243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43594344360691638368753495 65391516541037457553130243)
      ·
        refine ⟨98087274811556186329695365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65391516541037457553130243 98087274811556186329695365)
        ·
          refine ⟨18391364027166784936817881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98087274811556186329695365 18391364027166784936817881)
          ·
            refine ⟨13793523020375088702613411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18391364027166784936817881 13793523020375088702613411)
            ·
              refine ⟨20690284530562633053920117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13793523020375088702613411 20690284530562633053920117)
              ·
                refine ⟨1939714174740246848805011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20690284530562633053920117 1939714174740246848805011)
                ·
                  refine ⟨2909571262110370273207517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939714174740246848805011 2909571262110370273207517)
                  ·
                    refine ⟨1091089223291388852452819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2909571262110370273207517 1091089223291388852452819)
                    ·
                      rfl

theorem cell22_3187333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_3187333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187333 prefixEnd_3187333 := by exact prefixLift 3187333
  have htrace : WordTrace (prefixWord ++ tailWord_3187333) baseStart_3187333 baseEnd_3187333 := by
    simpa [prefixWord, tailWord_3187333, baseEnd_3187333] using wordTrace_append hprefix tailTrace_3187333
  have hstable : (prefixWord ++ tailWord_3187333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187333).length < 2 ^ (prefixWord ++ tailWord_3187333).sum := by decide
  have hdescent : baseEnd_3187333 < baseStart_3187333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187346 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 7]
def baseStart_3187346 : Nat := 118140960795 + 3187346 * 2 ^ 59
def prefixEnd_3187346 : Nat := 4983230072969 + 3 ^ 40 * 3187346 * 2
def baseEnd_3187346 : Nat := 363697891152353717292593

theorem tailTrace_3187346 : CollatzResearch.WordTrace tailWord_3187346 prefixEnd_3187346 363697891152353717292593 := by
  unfold tailWord_3187346
  simp only [CollatzResearch.WordTrace]
  refine ⟨29063014777699318050891473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77501372740531514802377261 29063014777699318050891473)
  ·
    refine ⟨21797261083274488538168605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29063014777699318050891473 21797261083274488538168605)
    ·
      refine ⟨8173972906227933201813227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21797261083274488538168605 8173972906227933201813227)
      ·
        refine ⟨12260959359341899802719841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8173972906227933201813227 12260959359341899802719841)
        ·
          refine ⟨9195719519506424852039881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12260959359341899802719841 9195719519506424852039881)
          ·
            refine ⟨6896789639629818639029911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9195719519506424852039881 6896789639629818639029911)
            ·
              refine ⟨10345184459444727958544867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6896789639629818639029911 10345184459444727958544867)
              ·
                refine ⟨15517776689167091937817301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10345184459444727958544867 15517776689167091937817301)
                ·
                  refine ⟨363697891152353717292593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15517776689167091937817301 363697891152353717292593)
                  ·
                    rfl

theorem cell22_3187346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_3187346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187346 prefixEnd_3187346 := by exact prefixLift 3187346
  have htrace : WordTrace (prefixWord ++ tailWord_3187346) baseStart_3187346 baseEnd_3187346 := by
    simpa [prefixWord, tailWord_3187346, baseEnd_3187346] using wordTrace_append hprefix tailTrace_3187346
  have hstable : (prefixWord ++ tailWord_3187346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187346).length < 2 ^ (prefixWord ++ tailWord_3187346).sum := by decide
  have hdescent : baseEnd_3187346 < baseStart_3187346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187423 : List Nat := [1, 1, 2, 3, 2, 4, 1, 3, 2, 3]
def baseStart_3187423 : Nat := 118140960795 + 3187423 * 2 ^ 59
def prefixEnd_3187423 : Nat := 4983230072969 + 3 ^ 40 * 3187423 * 2
def baseEnd_3187423 : Nat := 1091120032130658617702543

theorem tailTrace_3187423 : CollatzResearch.WordTrace tailWord_3187423 prefixEnd_3187423 1091120032130658617702543 := by
  unfold tailWord_3187423
  simp only [CollatzResearch.WordTrace]
  refine ⟨116254867531518314354118923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77503245021012209569412615 116254867531518314354118923)
  ·
    refine ⟨174382301297277471531178385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116254867531518314354118923 174382301297277471531178385)
    ·
      refine ⟨130786725972958103648383789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174382301297277471531178385 130786725972958103648383789)
      ·
        refine ⟨49045022239859288868143921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130786725972958103648383789 49045022239859288868143921)
        ·
          refine ⟨36783766679894466651107941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49045022239859288868143921 36783766679894466651107941)
          ·
            refine ⟨6896956252480212497082739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36783766679894466651107941 6896956252480212497082739)
            ·
              refine ⟨10345434378720318745624109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6896956252480212497082739 10345434378720318745624109)
              ·
                refine ⟨3879537892020119529609041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10345434378720318745624109 3879537892020119529609041)
                ·
                  refine ⟨2909653419015089647206781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3879537892020119529609041 2909653419015089647206781)
                  ·
                    refine ⟨1091120032130658617702543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2909653419015089647206781 1091120032130658617702543)
                    ·
                      rfl

theorem cell22_3187423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 3].length) (baseStart_3187423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187423 prefixEnd_3187423 := by exact prefixLift 3187423
  have htrace : WordTrace (prefixWord ++ tailWord_3187423) baseStart_3187423 baseEnd_3187423 := by
    simpa [prefixWord, tailWord_3187423, baseEnd_3187423] using wordTrace_append hprefix tailTrace_3187423
  have hstable : (prefixWord ++ tailWord_3187423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187423).length < 2 ^ (prefixWord ++ tailWord_3187423).sum := by decide
  have hdescent : baseEnd_3187423 < baseStart_3187423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187438 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3187438 : Nat := 118140960795 + 3187438 * 2 ^ 59
def prefixEnd_3187438 : Nat := 4983230072969 + 3 ^ 40 * 3187438 * 2
def baseEnd_3187438 : Nat := 1091125166937203578577497

theorem tailTrace_3187438 : CollatzResearch.WordTrace tailWord_3187438 prefixEnd_3187438 1091125166937203578577497 := by
  unfold tailWord_3187438
  simp only [CollatzResearch.WordTrace]
  refine ⟨14531926828307996489489371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77503609750975981277276645 14531926828307996489489371)
  ·
    refine ⟨21797890242461994734234057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14531926828307996489489371 21797890242461994734234057)
    ·
      refine ⟨16348417681846496050675543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21797890242461994734234057 16348417681846496050675543)
      ·
        refine ⟨24522626522769744076013315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16348417681846496050675543 24522626522769744076013315)
        ·
          refine ⟨36783939784154616114019973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24522626522769744076013315 36783939784154616114019973)
          ·
            refine ⟨6896988709528990521378745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36783939784154616114019973 6896988709528990521378745)
            ·
              refine ⟨5172741532146742891034059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6896988709528990521378745 5172741532146742891034059)
              ·
                refine ⟨7759112298220114336551089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5172741532146742891034059 7759112298220114336551089)
                ·
                  refine ⟨5819334223665085752413317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7759112298220114336551089 5819334223665085752413317)
                  ·
                    refine ⟨1091125166937203578577497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5819334223665085752413317 1091125166937203578577497)
                    ·
                      rfl

theorem cell22_3187438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3187438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187438 prefixEnd_3187438 := by exact prefixLift 3187438
  have htrace : WordTrace (prefixWord ++ tailWord_3187438) baseStart_3187438 baseEnd_3187438 := by
    simpa [prefixWord, tailWord_3187438, baseEnd_3187438] using wordTrace_append hprefix tailTrace_3187438
  have hstable : (prefixWord ++ tailWord_3187438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187438).length < 2 ^ (prefixWord ++ tailWord_3187438).sum := by decide
  have hdescent : baseEnd_3187438 < baseStart_3187438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187444 : List Nat := [2, 6, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3187444 : Nat := 118140960795 + 3187444 * 2 ^ 59
def prefixEnd_3187444 : Nat := 4983230072969 + 3 ^ 40 * 3187444 * 2
def baseEnd_3187444 : Nat := 1091127220859821562927479

theorem tailTrace_3187444 : CollatzResearch.WordTrace tailWord_3187444 prefixEnd_3187444 1091127220859821562927479 := by
  unfold tailWord_3187444
  simp only [CollatzResearch.WordTrace]
  refine ⟨58127816732221117470316693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77503755642961489960422257 58127816732221117470316693)
  ·
    refine ⟨2724741409322864881421095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58127816732221117470316693 2724741409322864881421095)
    ·
      refine ⟨4087112113984297322131643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2724741409322864881421095 4087112113984297322131643)
      ·
        refine ⟨6130668170976445983197465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4087112113984297322131643 6130668170976445983197465)
        ·
          refine ⟨4598001128232334487398099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6130668170976445983197465 4598001128232334487398099)
          ·
            refine ⟨6897001692348501731097149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4598001128232334487398099 6897001692348501731097149)
            ·
              refine ⟨2586375634630688149161431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6897001692348501731097149 2586375634630688149161431)
              ·
                refine ⟨3879563451946032223742147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2586375634630688149161431 3879563451946032223742147)
                ·
                  refine ⟨5819345177919048335613221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3879563451946032223742147 5819345177919048335613221)
                  ·
                    refine ⟨1091127220859821562927479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5819345177919048335613221 1091127220859821562927479)
                    ·
                      rfl

theorem cell22_3187444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3187444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187444 prefixEnd_3187444 := by exact prefixLift 3187444
  have htrace : WordTrace (prefixWord ++ tailWord_3187444) baseStart_3187444 baseEnd_3187444 := by
    simpa [prefixWord, tailWord_3187444, baseEnd_3187444] using wordTrace_append hprefix tailTrace_3187444
  have hstable : (prefixWord ++ tailWord_3187444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187444).length < 2 ^ (prefixWord ++ tailWord_3187444).sum := by decide
  have hdescent : baseEnd_3187444 < baseStart_3187444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187449 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 4, 6]
def baseStart_3187449 : Nat := 118140960795 + 3187449 * 2 ^ 59
def prefixEnd_3187449 : Nat := 4983230072969 + 3 ^ 40 * 3187449 * 2
def baseEnd_3187449 : Nat := 1091128932462003216552463

theorem tailTrace_3187449 : CollatzResearch.WordTrace tailWord_3187449 prefixEnd_3187449 1091128932462003216552463 := by
  unfold tailWord_3187449
  simp only [CollatzResearch.WordTrace]
  refine ⟨116255815829424120794565401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77503877219616080529710267 116255815829424120794565401)
  ·
    refine ⟨87191861872068090595924051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116255815829424120794565401 87191861872068090595924051)
    ·
      refine ⟨130787792808102135893886077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87191861872068090595924051 130787792808102135893886077)
      ·
        refine ⟨49045422303038300960207279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130787792808102135893886077 49045422303038300960207279)
        ·
          refine ⟨73568133454557451440310919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49045422303038300960207279 73568133454557451440310919)
          ·
            refine ⟨110352200181836177160466379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73568133454557451440310919 110352200181836177160466379)
            ·
              refine ⟨165528300272754265740699569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110352200181836177160466379 165528300272754265740699569)
              ·
                refine ⟨124146225204565699305524677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165528300272754265740699569 124146225204565699305524677)
                ·
                  refine ⟨23277417225856068619785877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124146225204565699305524677 23277417225856068619785877)
                  ·
                    refine ⟨1091128932462003216552463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23277417225856068619785877 1091128932462003216552463)
                    ·
                      rfl

theorem cell22_3187449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_3187449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187449 prefixEnd_3187449 := by exact prefixLift 3187449
  have htrace : WordTrace (prefixWord ++ tailWord_3187449) baseStart_3187449 baseEnd_3187449 := by
    simpa [prefixWord, tailWord_3187449, baseEnd_3187449] using wordTrace_append hprefix tailTrace_3187449
  have hstable : (prefixWord ++ tailWord_3187449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187449).length < 2 ^ (prefixWord ++ tailWord_3187449).sum := by decide
  have hdescent : baseEnd_3187449 < baseStart_3187449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187496 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 1, 7]
def baseStart_3187496 : Nat := 118140960795 + 3187496 * 2 ^ 59
def prefixEnd_3187496 : Nat := 4983230072969 + 3 ^ 40 * 3187496 * 2
def baseEnd_3187496 : Nat := 1091145021522510760627319

theorem tailTrace_3187496 : CollatzResearch.WordTrace tailWord_3187496 prefixEnd_3187496 1091145021522510760627319 := by
  unfold tailWord_3187496
  simp only [CollatzResearch.WordTrace]
  refine ⟨58128765030126923910763171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77505020040169231881017561 58128765030126923910763171)
  ·
    refine ⟨87193147545190385866144757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58128765030126923910763171 87193147545190385866144757)
    ·
      refine ⟨8174357582361598674951071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87193147545190385866144757 8174357582361598674951071)
      ·
        refine ⟨12261536373542398012426607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8174357582361598674951071 12261536373542398012426607)
        ·
          refine ⟨18392304560313597018639911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12261536373542398012426607 18392304560313597018639911)
          ·
            refine ⟨27588456840470395527959867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18392304560313597018639911 27588456840470395527959867)
            ·
              refine ⟨41382685260705593291939801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27588456840470395527959867 41382685260705593291939801)
              ·
                refine ⟨31037013945529194968954851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41382685260705593291939801 31037013945529194968954851)
                ·
                  refine ⟨46555520918293792453432277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31037013945529194968954851 46555520918293792453432277)
                  ·
                    refine ⟨1091145021522510760627319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46555520918293792453432277 1091145021522510760627319)
                    ·
                      rfl

theorem cell22_3187496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_3187496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187496 prefixEnd_3187496 := by exact prefixLift 3187496
  have htrace : WordTrace (prefixWord ++ tailWord_3187496) baseStart_3187496 baseEnd_3187496 := by
    simpa [prefixWord, tailWord_3187496, baseEnd_3187496] using wordTrace_append hprefix tailTrace_3187496
  have hstable : (prefixWord ++ tailWord_3187496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187496).length < 2 ^ (prefixWord ++ tailWord_3187496).sum := by decide
  have hdescent : baseEnd_3187496 < baseStart_3187496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187502 : List Nat := [4, 1, 3, 2, 1, 1, 1, 5, 1, 3]
def baseStart_3187502 : Nat := 118140960795 + 3187502 * 2 ^ 59
def prefixEnd_3187502 : Nat := 4983230072969 + 3 ^ 40 * 3187502 * 2
def baseEnd_3187502 : Nat := 1091147075445128744977301

theorem tailTrace_3187502 : CollatzResearch.WordTrace tailWord_3187502 prefixEnd_3187502 1091147075445128744977301 := by
  unfold tailWord_3187502
  simp only [CollatzResearch.WordTrace]
  refine ⟨14532218612279013855780595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77505165932154740564163173 14532218612279013855780595)
  ·
    refine ⟨21798327918418520783670893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14532218612279013855780595 21798327918418520783670893)
    ·
      refine ⟨8174372969406945293876585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21798327918418520783670893 8174372969406945293876585)
      ·
        refine ⟨6130779727055208970407439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8174372969406945293876585 6130779727055208970407439)
        ·
          refine ⟨9196169590582813455611159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6130779727055208970407439 9196169590582813455611159)
          ·
            refine ⟨13794254385874220183416739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9196169590582813455611159 13794254385874220183416739)
            ·
              refine ⟨20691381578811330275125109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13794254385874220183416739 20691381578811330275125109)
              ·
                refine ⟨1939817023013562213292979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20691381578811330275125109 1939817023013562213292979)
                ·
                  refine ⟨2909725534520343319939469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939817023013562213292979 2909725534520343319939469)
                  ·
                    refine ⟨1091147075445128744977301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2909725534520343319939469 1091147075445128744977301)
                    ·
                      rfl

theorem cell22_3187502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_3187502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187502 prefixEnd_3187502 := by exact prefixLift 3187502
  have htrace : WordTrace (prefixWord ++ tailWord_3187502) baseStart_3187502 baseEnd_3187502 := by
    simpa [prefixWord, tailWord_3187502, baseEnd_3187502] using wordTrace_append hprefix tailTrace_3187502
  have hstable : (prefixWord ++ tailWord_3187502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187502).length < 2 ^ (prefixWord ++ tailWord_3187502).sum := by decide
  have hdescent : baseEnd_3187502 < baseStart_3187502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187560 : List Nat := [2, 1, 4, 2, 1, 2, 3, 3, 4]
def baseStart_3187560 : Nat := 118140960795 + 3187560 * 2 ^ 59
def prefixEnd_3187560 : Nat := 4983230072969 + 3 ^ 40 * 3187560 * 2
def baseEnd_3187560 : Nat := 363722310010145309009041

theorem tailTrace_3187560 : CollatzResearch.WordTrace tailWord_3187560 prefixEnd_3187560 363722310010145309009041 := by
  unfold tailWord_3187560
  simp only [CollatzResearch.WordTrace]
  refine ⟨58129932166010993375928067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77506576221347991167904089 58129932166010993375928067)
  ·
    refine ⟨87194898249016490063892101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58129932166010993375928067 87194898249016490063892101)
    ·
      refine ⟨16349043421690591886979769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87194898249016490063892101 16349043421690591886979769)
      ·
        refine ⟨12261782566267943915234827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16349043421690591886979769 12261782566267943915234827)
        ·
          refine ⟨18392673849401915872852241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12261782566267943915234827 18392673849401915872852241)
          ·
            refine ⟨13794505387051436904639181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18392673849401915872852241 13794505387051436904639181)
            ·
              refine ⟨5172939520144288839239693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13794505387051436904639181 5172939520144288839239693)
              ·
                refine ⟨1939852320054108314714885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5172939520144288839239693 1939852320054108314714885)
                ·
                  refine ⟨363722310010145309009041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1939852320054108314714885 363722310010145309009041)
                  ·
                    rfl

theorem cell22_3187560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 4].length) (baseStart_3187560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187560 prefixEnd_3187560 := by exact prefixLift 3187560
  have htrace : WordTrace (prefixWord ++ tailWord_3187560) baseStart_3187560 baseEnd_3187560 := by
    simpa [prefixWord, tailWord_3187560, baseEnd_3187560] using wordTrace_append hprefix tailTrace_3187560
  have hstable : (prefixWord ++ tailWord_3187560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187560).length < 2 ^ (prefixWord ++ tailWord_3187560).sum := by decide
  have hdescent : baseEnd_3187560 < baseStart_3187560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187573 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3187573 : Nat := 118140960795 + 3187573 * 2 ^ 59
def prefixEnd_3187573 : Nat := 4983230072969 + 3 ^ 40 * 3187573 * 2
def baseEnd_3187573 : Nat := 1091171380196108226452083

theorem tailTrace_3187573 : CollatzResearch.WordTrace tailWord_3187573 prefixEnd_3187573 1091171380196108226452083 := by
  unfold tailWord_3187573
  simp only [CollatzResearch.WordTrace]
  refine ⟨116260338480974889972079373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77506892320649926648052915 116260338480974889972079373)
  ·
    refine ⟨43597626930365583739529765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116260338480974889972079373 43597626930365583739529765)
    ·
      refine ⟨8174555049443546951161831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43597626930365583739529765 8174555049443546951161831)
      ·
        refine ⟨12261832574165320426742747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8174555049443546951161831 12261832574165320426742747)
        ·
          refine ⟨18392748861247980640114121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12261832574165320426742747 18392748861247980640114121)
          ·
            refine ⟨13794561645935985480085591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18392748861247980640114121 13794561645935985480085591)
            ·
              refine ⟨20691842468903978220128387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13794561645935985480085591 20691842468903978220128387)
              ·
                refine ⟨31037763703355967330192581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20691842468903978220128387 31037763703355967330192581)
                ·
                  refine ⟨5819580694379243874411109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31037763703355967330192581 5819580694379243874411109)
                  ·
                    refine ⟨1091171380196108226452083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5819580694379243874411109 1091171380196108226452083)
                    ·
                      rfl

theorem cell22_3187573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3187573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187573 prefixEnd_3187573 := by exact prefixLift 3187573
  have htrace : WordTrace (prefixWord ++ tailWord_3187573) baseStart_3187573 baseEnd_3187573 := by
    simpa [prefixWord, tailWord_3187573, baseEnd_3187573] using wordTrace_append hprefix tailTrace_3187573
  have hstable : (prefixWord ++ tailWord_3187573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187573).length < 2 ^ (prefixWord ++ tailWord_3187573).sum := by decide
  have hdescent : baseEnd_3187573 < baseStart_3187573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187592 : List Nat := [2, 1, 3, 3, 2, 1, 4, 1, 2, 3]
def baseStart_3187592 : Nat := 118140960795 + 3187592 * 2 ^ 59
def prefixEnd_3187592 : Nat := 4983230072969 + 3 ^ 40 * 3187592 * 2
def baseEnd_3187592 : Nat := 1091177884284398510227025

theorem tailTrace_3187592 : CollatzResearch.WordTrace tailWord_3187592 prefixEnd_3187592 1091177884284398510227025 := by
  unfold tailWord_3187592
  simp only [CollatzResearch.WordTrace]
  refine ⟨58130515733953028108510515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77507354311937370811347353 58130515733953028108510515)
  ·
    refine ⟨87195773600929542162765773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58130515733953028108510515 87195773600929542162765773)
    ·
      refine ⟨32698415100348578311037165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87195773600929542162765773 32698415100348578311037165)
      ·
        refine ⟨12261905662630716866638937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32698415100348578311037165 12261905662630716866638937)
        ·
          refine ⟨9196429246973037649979203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12261905662630716866638937 9196429246973037649979203)
          ·
            refine ⟨13794643870459556474968805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9196429246973037649979203 13794643870459556474968805)
            ·
              refine ⟨2586495725711166839056651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13794643870459556474968805 2586495725711166839056651)
              ·
                refine ⟨3879743588566750258584977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2586495725711166839056651 3879743588566750258584977)
                ·
                  refine ⟨2909807691425062693938733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3879743588566750258584977 2909807691425062693938733)
                  ·
                    refine ⟨1091177884284398510227025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2909807691425062693938733 1091177884284398510227025)
                    ·
                      rfl

theorem cell22_3187592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_3187592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187592 prefixEnd_3187592 := by exact prefixLift 3187592
  have htrace : WordTrace (prefixWord ++ tailWord_3187592) baseStart_3187592 baseEnd_3187592 := by
    simpa [prefixWord, tailWord_3187592, baseEnd_3187592] using wordTrace_append hprefix tailTrace_3187592
  have hstable : (prefixWord ++ tailWord_3187592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187592).length < 2 ^ (prefixWord ++ tailWord_3187592).sum := by decide
  have hdescent : baseEnd_3187592 < baseStart_3187592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187616 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 9]
def baseStart_3187616 : Nat := 118140960795 + 3187616 * 2 ^ 59
def prefixEnd_3187616 : Nat := 4983230072969 + 3 ^ 40 * 3187616 * 2
def baseEnd_3187616 : Nat := 363728699991623482542317

theorem tailTrace_3187616 : CollatzResearch.WordTrace tailWord_3187616 prefixEnd_3187616 363728699991623482542317 := by
  unfold tailWord_3187616
  simp only [CollatzResearch.WordTrace]
  refine ⟨58130953409909554157947351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77507937879879405543929801 58130953409909554157947351)
  ·
    refine ⟨87196430114864331236921027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58130953409909554157947351 87196430114864331236921027)
    ·
      refine ⟨130794645172296496855381541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87196430114864331236921027 130794645172296496855381541)
      ·
        refine ⟨24523995969805593160384039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130794645172296496855381541 24523995969805593160384039)
        ·
          refine ⟨36785993954708389740576059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24523995969805593160384039 36785993954708389740576059)
          ·
            refine ⟨55178990932062584610864089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36785993954708389740576059 55178990932062584610864089)
            ·
              refine ⟨41384243199046938458148067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55178990932062584610864089 41384243199046938458148067)
              ·
                refine ⟨62076364798570407687222101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41384243199046938458148067 62076364798570407687222101)
                ·
                  refine ⟨363728699991623482542317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62076364798570407687222101 363728699991623482542317)
                  ·
                    rfl

theorem cell22_3187616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_3187616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187616 prefixEnd_3187616 := by exact prefixLift 3187616
  have htrace : WordTrace (prefixWord ++ tailWord_3187616) baseStart_3187616 baseEnd_3187616 := by
    simpa [prefixWord, tailWord_3187616, baseEnd_3187616] using wordTrace_append hprefix tailTrace_3187616
  have hstable : (prefixWord ++ tailWord_3187616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187616).length < 2 ^ (prefixWord ++ tailWord_3187616).sum := by decide
  have hdescent : baseEnd_3187616 < baseStart_3187616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187637 : List Nat := [1, 3, 3, 2, 1, 1, 3, 4, 1, 3]
def baseStart_3187637 : Nat := 118140960795 + 3187637 * 2 ^ 59
def prefixEnd_3187637 : Nat := 4983230072969 + 3 ^ 40 * 3187637 * 2
def baseEnd_3187637 : Nat := 1091193288704033392851887

theorem tailTrace_3187637 : CollatzResearch.WordTrace tailWord_3187637 prefixEnd_3187637 1091193288704033392851887 := by
  unfold tailWord_3187637
  simp only [CollatzResearch.WordTrace]
  refine ⟨116262672752743028902409165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77508448501828685934939443 116262672752743028902409165)
  ·
    refine ⟨43598502282278635838403437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116262672752743028902409165 43598502282278635838403437)
    ·
      refine ⟨16349438355854488439401289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43598502282278635838403437 16349438355854488439401289)
      ·
        refine ⟨12262078766890866329550967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16349438355854488439401289 12262078766890866329550967)
        ·
          refine ⟨18393118150336299494326451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12262078766890866329550967 18393118150336299494326451)
          ·
            refine ⟨27589677225504449241489677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18393118150336299494326451 27589677225504449241489677)
            ·
              refine ⟨10346128959564168465558629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27589677225504449241489677 10346128959564168465558629)
              ·
                refine ⟨1939899179918281587292243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10346128959564168465558629 1939899179918281587292243)
                ·
                  refine ⟨2909848769877422380938365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939899179918281587292243 2909848769877422380938365)
                  ·
                    refine ⟨1091193288704033392851887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2909848769877422380938365 1091193288704033392851887)
                    ·
                      rfl

theorem cell22_3187637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_3187637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187637 prefixEnd_3187637 := by exact prefixLift 3187637
  have htrace : WordTrace (prefixWord ++ tailWord_3187637) baseStart_3187637 baseEnd_3187637 := by
    simpa [prefixWord, tailWord_3187637, baseEnd_3187637] using wordTrace_append hprefix tailTrace_3187637
  have hstable : (prefixWord ++ tailWord_3187637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187637).length < 2 ^ (prefixWord ++ tailWord_3187637).sum := by decide
  have hdescent : baseEnd_3187637 < baseStart_3187637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187648 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 2, 5]
def baseStart_3187648 : Nat := 118140960795 + 3187648 * 2 ^ 59
def prefixEnd_3187648 : Nat := 4983230072969 + 3 ^ 40 * 3187648 * 2
def baseEnd_3187648 : Nat := 1091197054228833030826853

theorem tailTrace_3187648 : CollatzResearch.WordTrace tailWord_3187648 prefixEnd_3187648 1091197054228833030826853 := by
  unfold tailWord_3187648
  simp only [CollatzResearch.WordTrace]
  refine ⟨58131536977851588890529799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77508715970468785187373065 58131536977851588890529799)
  ·
    refine ⟨87197305466777383335794699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58131536977851588890529799 87197305466777383335794699)
    ·
      refine ⟨130795958200166075003692049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87197305466777383335794699 130795958200166075003692049)
      ·
        refine ⟨98096968650124556252769037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130795958200166075003692049 98096968650124556252769037)
        ·
          refine ⟨36786363243796708594788389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98096968650124556252769037 36786363243796708594788389)
          ·
            refine ⟨6897443108211882861522823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36786363243796708594788389 6897443108211882861522823)
            ·
              refine ⟨10346164662317824292284235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6897443108211882861522823 10346164662317824292284235)
              ·
                refine ⟨15519246993476736438426353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10346164662317824292284235 15519246993476736438426353)
                ·
                  refine ⟨11639435245107552328819765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15519246993476736438426353 11639435245107552328819765)
                  ·
                    refine ⟨1091197054228833030826853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11639435245107552328819765 1091197054228833030826853)
                    ·
                      rfl

theorem cell22_3187648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_3187648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187648 prefixEnd_3187648 := by exact prefixLift 3187648
  have htrace : WordTrace (prefixWord ++ tailWord_3187648) baseStart_3187648 baseEnd_3187648 := by
    simpa [prefixWord, tailWord_3187648, baseEnd_3187648] using wordTrace_append hprefix tailTrace_3187648
  have hstable : (prefixWord ++ tailWord_3187648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187648).length < 2 ^ (prefixWord ++ tailWord_3187648).sum := by decide
  have hdescent : baseEnd_3187648 < baseStart_3187648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187663 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 3, 4]
def baseStart_3187663 : Nat := 118140960795 + 3187663 * 2 ^ 59
def prefixEnd_3187663 : Nat := 4983230072969 + 3 ^ 40 * 3187663 * 2
def baseEnd_3187663 : Nat := 1091202189035377991701807

theorem tailTrace_3187663 : CollatzResearch.WordTrace tailWord_3187663 prefixEnd_3187663 1091202189035377991701807 := by
  unfold tailWord_3187663
  simp only [CollatzResearch.WordTrace]
  refine ⟨116263621050648835342855643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77509080700432556895237095 116263621050648835342855643)
  ·
    refine ⟨174395431575973253014283465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116263621050648835342855643 174395431575973253014283465)
    ·
      refine ⟨130796573681979939760712599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174395431575973253014283465 130796573681979939760712599)
      ·
        refine ⟨196194860522969909641068899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130796573681979939760712599 196194860522969909641068899)
        ·
          refine ⟨294292290784454864461603349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196194860522969909641068899 294292290784454864461603349)
          ·
            refine ⟨13794951130521321771637657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 294292290784454864461603349 13794951130521321771637657)
            ·
              refine ⟨10346213347890991328728243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13794951130521321771637657 10346213347890991328728243)
              ·
                refine ⟨15519320021836486993092365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10346213347890991328728243 15519320021836486993092365)
                ·
                  refine ⟨5819745008188682622409637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15519320021836486993092365 5819745008188682622409637)
                  ·
                    refine ⟨1091202189035377991701807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5819745008188682622409637 1091202189035377991701807)
                    ·
                      rfl

theorem cell22_3187663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_3187663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187663 prefixEnd_3187663 := by exact prefixLift 3187663
  have htrace : WordTrace (prefixWord ++ tailWord_3187663) baseStart_3187663 baseEnd_3187663 := by
    simpa [prefixWord, tailWord_3187663, baseEnd_3187663] using wordTrace_append hprefix tailTrace_3187663
  have hstable : (prefixWord ++ tailWord_3187663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187663).length < 2 ^ (prefixWord ++ tailWord_3187663).sum := by decide
  have hdescent : baseEnd_3187663 < baseStart_3187663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187695 : List Nat := [1, 1, 2, 1, 4, 3, 2, 4, 4]
def baseStart_3187695 : Nat := 118140960795 + 3187695 * 2 ^ 59
def prefixEnd_3187695 : Nat := 4983230072969 + 3 ^ 40 * 3187695 * 2
def baseEnd_3187695 : Nat := 363737714429780191633903

theorem tailTrace_3187695 : CollatzResearch.WordTrace tailWord_3187695 prefixEnd_3187695 363737714429780191633903 := by
  unfold tailWord_3187695
  simp only [CollatzResearch.WordTrace]
  refine ⟨116264788186532904808020539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77509858791021936538680359 116264788186532904808020539)
  ·
    refine ⟨174397182279799357212030809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116264788186532904808020539 174397182279799357212030809)
    ·
      refine ⟨130797886709849517909023107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174397182279799357212030809 130797886709849517909023107)
      ·
        refine ⟨196196830064774276863534661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130797886709849517909023107 196196830064774276863534661)
        ·
          refine ⟨36786905637145176911912749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196196830064774276863534661 36786905637145176911912749)
          ·
            refine ⟨13795089613929441341967281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36786905637145176911912749 13795089613929441341967281)
            ·
              refine ⟨10346317210447081006475461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13795089613929441341967281 10346317210447081006475461)
              ·
                refine ⟨1939934476958827688714149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10346317210447081006475461 1939934476958827688714149)
                ·
                  refine ⟨363737714429780191633903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1939934476958827688714149 363737714429780191633903)
                  ·
                    rfl

theorem cell22_3187695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 4].length) (baseStart_3187695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187695 prefixEnd_3187695 := by exact prefixLift 3187695
  have htrace : WordTrace (prefixWord ++ tailWord_3187695) baseStart_3187695 baseEnd_3187695 := by
    simpa [prefixWord, tailWord_3187695, baseEnd_3187695] using wordTrace_append hprefix tailTrace_3187695
  have hstable : (prefixWord ++ tailWord_3187695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187695).length < 2 ^ (prefixWord ++ tailWord_3187695).sum := by decide
  have hdescent : baseEnd_3187695 < baseStart_3187695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187708 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_3187708 : Nat := 118140960795 + 3187708 * 2 ^ 59
def prefixEnd_3187708 : Nat := 4983230072969 + 3 ^ 40 * 3187708 * 2
def baseEnd_3187708 : Nat := 1091217593455012874326669

theorem tailTrace_3187708 : CollatzResearch.WordTrace tailWord_3187708 prefixEnd_3187708 1091217593455012874326669 := by
  unfold tailWord_3187708
  simp only [CollatzResearch.WordTrace]
  refine ⟨58132631167742904014121889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77510174890323872018829185 58132631167742904014121889)
  ·
    refine ⟨43599473375807178010591417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58132631167742904014121889 43599473375807178010591417)
    ·
      refine ⟨32699605031855383507943563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43599473375807178010591417 32699605031855383507943563)
      ·
        refine ⟨49049407547783075261915345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32699605031855383507943563 49049407547783075261915345)
        ·
          refine ⟨36787055660837306446436509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49049407547783075261915345 36787055660837306446436509)
          ·
            refine ⟨13795145872813989917413691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36787055660837306446436509 13795145872813989917413691)
            ·
              refine ⟨20692718809220984876120537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13795145872813989917413691 20692718809220984876120537)
              ·
                refine ⟨15519539106915738657090403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20692718809220984876120537 15519539106915738657090403)
                ·
                  refine ⟨23279308660373607985635605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15519539106915738657090403 23279308660373607985635605)
                  ·
                    refine ⟨1091217593455012874326669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23279308660373607985635605 1091217593455012874326669)
                    ·
                      rfl

theorem cell22_3187708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_3187708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187708 prefixEnd_3187708 := by exact prefixLift 3187708
  have htrace : WordTrace (prefixWord ++ tailWord_3187708) baseStart_3187708 baseEnd_3187708 := by
    simpa [prefixWord, tailWord_3187708, baseEnd_3187708] using wordTrace_append hprefix tailTrace_3187708
  have hstable : (prefixWord ++ tailWord_3187708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187708).length < 2 ^ (prefixWord ++ tailWord_3187708).sum := by decide
  have hdescent : baseEnd_3187708 < baseStart_3187708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187723 : List Nat := [1, 1, 1, 1, 6, 3, 1, 8]
def baseStart_3187723 : Nat := 118140960795 + 3187723 * 2 ^ 59
def prefixEnd_3187723 : Nat := 4983230072969 + 3 ^ 40 * 3187723 * 2
def baseEnd_3187723 : Nat := 121246969806839759466847

theorem tailTrace_3187723 : CollatzResearch.WordTrace tailWord_3187723 prefixEnd_3187723 121246969806839759466847 := by
  unfold tailWord_3187723
  simp only [CollatzResearch.WordTrace]
  refine ⟨116265809430431465590039823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77510539620287643726693215 116265809430431465590039823)
  ·
    refine ⟨174398714145647198385059735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116265809430431465590039823 174398714145647198385059735)
    ·
      refine ⟨261598071218470797577589603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174398714145647198385059735 261598071218470797577589603)
      ·
        refine ⟨392397106827706196366384405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261598071218470797577589603 392397106827706196366384405)
        ·
          refine ⟨18393614382548727954674269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 392397106827706196366384405 18393614382548727954674269)
          ·
            refine ⟨6897605393455772983002851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18393614382548727954674269 6897605393455772983002851)
            ·
              refine ⟨10346408090183659474504277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6897605393455772983002851 10346408090183659474504277)
              ·
                refine ⟨121246969806839759466847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10346408090183659474504277 121246969806839759466847)
                ·
                  rfl

theorem cell22_3187723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 8].length) (baseStart_3187723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187723 prefixEnd_3187723 := by exact prefixLift 3187723
  have htrace : WordTrace (prefixWord ++ tailWord_3187723) baseStart_3187723 baseEnd_3187723 := by
    simpa [prefixWord, tailWord_3187723, baseEnd_3187723] using wordTrace_append hprefix tailTrace_3187723
  have hstable : (prefixWord ++ tailWord_3187723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187723).length < 2 ^ (prefixWord ++ tailWord_3187723).sum := by decide
  have hdescent : baseEnd_3187723 < baseStart_3187723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187740 : List Nat := [2, 2, 3, 1, 4, 2, 8]
def baseStart_3187740 : Nat := 118140960795 + 3187740 * 2 ^ 59
def prefixEnd_3187740 : Nat := 4983230072969 + 3 ^ 40 * 3187740 * 2
def baseEnd_3187740 : Nat := 40415872137369461389873

theorem tailTrace_3187740 : CollatzResearch.WordTrace tailWord_3187740 prefixEnd_3187740 40415872137369461389873 := by
  unfold tailWord_3187740
  simp only [CollatzResearch.WordTrace]
  refine ⟨58133214735684938746704337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77510952980913251662272449 58133214735684938746704337)
  ·
    refine ⟨43599911051763704060028253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58133214735684938746704337 43599911051763704060028253)
    ·
      refine ⟨16349966644411389022510595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43599911051763704060028253 16349966644411389022510595)
      ·
        refine ⟨24524949966617083533765893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16349966644411389022510595 24524949966617083533765893)
        ·
          refine ⟨4598428118740703162581105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24524949966617083533765893 4598428118740703162581105)
          ·
            refine ⟨3448821089055527371935829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4598428118740703162581105 3448821089055527371935829)
            ·
              refine ⟨40415872137369461389873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3448821089055527371935829 40415872137369461389873)
              ·
                rfl

theorem cell22_3187740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 8].length) (baseStart_3187740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187740 prefixEnd_3187740 := by exact prefixLift 3187740
  have htrace : WordTrace (prefixWord ++ tailWord_3187740) baseStart_3187740 baseEnd_3187740 := by
    simpa [prefixWord, tailWord_3187740, baseEnd_3187740] using wordTrace_append hprefix tailTrace_3187740
  have hstable : (prefixWord ++ tailWord_3187740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187740).length < 2 ^ (prefixWord ++ tailWord_3187740).sum := by decide
  have hdescent : baseEnd_3187740 < baseStart_3187740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187815 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 3, 4]
def baseStart_3187815 : Nat := 118140960795 + 3187815 * 2 ^ 59
def prefixEnd_3187815 : Nat := 4983230072969 + 3 ^ 40 * 3187815 * 2
def baseEnd_3187815 : Nat := 1091254221741700261901341

theorem tailTrace_3187815 : CollatzResearch.WordTrace tailWord_3187815 prefixEnd_3187815 1091254221741700261901341 := by
  unfold tailWord_3187815
  simp only [CollatzResearch.WordTrace]
  refine ⟨116269164946098165302388899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77512776630732110201592599 116269164946098165302388899)
  ·
    refine ⟨174403747419147247953583349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116269164946098165302388899 174403747419147247953583349)
    ·
      refine ⟨16350351320545054495648439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174403747419147247953583349 16350351320545054495648439)
      ·
        refine ⟨24525526980817581743472659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16350351320545054495648439 24525526980817581743472659)
        ·
          refine ⟨36788290471226372615208989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24525526980817581743472659 36788290471226372615208989)
          ·
            refine ⟨13795608926709889730703371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36788290471226372615208989 13795608926709889730703371)
            ·
              refine ⟨20693413390064834596055057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13795608926709889730703371 20693413390064834596055057)
              ·
                refine ⟨15520060042548625947041293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20693413390064834596055057 15520060042548625947041293)
                ·
                  refine ⟨5820022515955734730140485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15520060042548625947041293 5820022515955734730140485)
                  ·
                    refine ⟨1091254221741700261901341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5820022515955734730140485 1091254221741700261901341)
                    ·
                      rfl

theorem cell22_3187815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_3187815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187815 prefixEnd_3187815 := by exact prefixLift 3187815
  have htrace : WordTrace (prefixWord ++ tailWord_3187815) baseStart_3187815 baseEnd_3187815 := by
    simpa [prefixWord, tailWord_3187815, baseEnd_3187815] using wordTrace_append hprefix tailTrace_3187815
  have hstable : (prefixWord ++ tailWord_3187815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187815).length < 2 ^ (prefixWord ++ tailWord_3187815).sum := by decide
  have hdescent : baseEnd_3187815 < baseStart_3187815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187849 : List Nat := [1, 2, 1, 1, 4, 5, 2, 1, 1, 4]
def baseStart_3187849 : Nat := 118140960795 + 3187849 * 2 ^ 59
def prefixEnd_3187849 : Nat := 4983230072969 + 3 ^ 40 * 3187849 * 2
def baseEnd_3187849 : Nat := 1091265860636535506551237

theorem tailTrace_3187849 : CollatzResearch.WordTrace tailWord_3187849 prefixEnd_3187849 1091265860636535506551237 := by
  unfold tailWord_3187849
  simp only [CollatzResearch.WordTrace]
  refine ⟨116270405027974989109126601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77513603351983326072751067 116270405027974989109126601)
  ·
    refine ⟨87202803770981241831844951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116270405027974989109126601 87202803770981241831844951)
    ·
      refine ⟨130804205656471862747767427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87202803770981241831844951 130804205656471862747767427)
      ·
        refine ⟨196206308484707794121651141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130804205656471862747767427 196206308484707794121651141)
        ·
          refine ⟨36788682840882711397809589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196206308484707794121651141 36788682840882711397809589)
          ·
            refine ⟨3448939016332754193544649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36788682840882711397809589 3448939016332754193544649)
            ·
              refine ⟨2586704262249565645158487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3448939016332754193544649 2586704262249565645158487)
              ·
                refine ⟨3880056393374348467737731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2586704262249565645158487 3880056393374348467737731)
                ·
                  refine ⟨5820084590061522701606597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3880056393374348467737731 5820084590061522701606597)
                  ·
                    refine ⟨1091265860636535506551237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5820084590061522701606597 1091265860636535506551237)
                    ·
                      rfl

theorem cell22_3187849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 1, 4].length) (baseStart_3187849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187849 prefixEnd_3187849 := by exact prefixLift 3187849
  have htrace : WordTrace (prefixWord ++ tailWord_3187849) baseStart_3187849 baseEnd_3187849 := by
    simpa [prefixWord, tailWord_3187849, baseEnd_3187849] using wordTrace_append hprefix tailTrace_3187849
  have hstable : (prefixWord ++ tailWord_3187849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187849).length < 2 ^ (prefixWord ++ tailWord_3187849).sum := by decide
  have hdescent : baseEnd_3187849 < baseStart_3187849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187879 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3187879 : Nat := 118140960795 + 3187879 * 2 ^ 59
def prefixEnd_3187879 : Nat := 4983230072969 + 3 ^ 40 * 3187879 * 2
def baseEnd_3187879 : Nat := 1091276130249625428301145

theorem tailTrace_3187879 : CollatzResearch.WordTrace tailWord_3187879 prefixEnd_3187879 1091276130249625428301145 := by
  unfold tailWord_3187879
  simp only [CollatzResearch.WordTrace]
  refine ⟨116271499217866304232718691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77514332811910869488479127 116271499217866304232718691)
  ·
    refine ⟨174407248826799456349078037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116271499217866304232718691 174407248826799456349078037)
    ·
      refine ⟨8175339788756224516363033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174407248826799456349078037 8175339788756224516363033)
      ·
        refine ⟨6131504841567168387272275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8175339788756224516363033 6131504841567168387272275)
        ·
          refine ⟨9197257262350752580908413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6131504841567168387272275 9197257262350752580908413)
          ·
            refine ⟨3448971473381532217840655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9197257262350752580908413 3448971473381532217840655)
            ·
              refine ⟨5173457210072298326760983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448971473381532217840655 5173457210072298326760983)
              ·
                refine ⟨7760185815108447490141475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5173457210072298326760983 7760185815108447490141475)
                ·
                  refine ⟨11640278722662671235212213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7760185815108447490141475 11640278722662671235212213)
                  ·
                    refine ⟨1091276130249625428301145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11640278722662671235212213 1091276130249625428301145)
                    ·
                      rfl

theorem cell22_3187879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3187879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187879 prefixEnd_3187879 := by exact prefixLift 3187879
  have htrace : WordTrace (prefixWord ++ tailWord_3187879) baseStart_3187879 baseEnd_3187879 := by
    simpa [prefixWord, tailWord_3187879, baseEnd_3187879] using wordTrace_append hprefix tailTrace_3187879
  have hstable : (prefixWord ++ tailWord_3187879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187879).length < 2 ^ (prefixWord ++ tailWord_3187879).sum := by decide
  have hdescent : baseEnd_3187879 < baseStart_3187879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187935 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 2, 5]
def baseStart_3187935 : Nat := 118140960795 + 3187935 * 2 ^ 59
def prefixEnd_3187935 : Nat := 4983230072969 + 3 ^ 40 * 3187935 * 2
def baseEnd_3187935 : Nat := 1091295300194059948900973

theorem tailTrace_3187935 : CollatzResearch.WordTrace tailWord_3187935 prefixEnd_3187935 1091295300194059948900973 := by
  unfold tailWord_3187935
  simp only [CollatzResearch.WordTrace]
  refine ⟨116273541705663425796757259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77515694470442283864504839 116273541705663425796757259)
  ·
    refine ⟨174410312558495138695135889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116273541705663425796757259 174410312558495138695135889)
    ·
      refine ⟨130807734418871354021351917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174410312558495138695135889 130807734418871354021351917)
      ·
        refine ⟨49052900407076757758006969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130807734418871354021351917 49052900407076757758006969)
        ·
          refine ⟨36789675305307568318505227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49052900407076757758006969 36789675305307568318505227)
          ·
            refine ⟨55184512957961352477757841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36789675305307568318505227 55184512957961352477757841)
            ·
              refine ⟨41388384718471014358318381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55184512957961352477757841 41388384718471014358318381)
              ·
                refine ⟨15520644269426630384369393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41388384718471014358318381 15520644269426630384369393)
                ·
                  refine ⟨11640483202069972788277045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15520644269426630384369393 11640483202069972788277045)
                  ·
                    refine ⟨1091295300194059948900973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11640483202069972788277045 1091295300194059948900973)
                    ·
                      rfl

theorem cell22_3187935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_3187935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187935 prefixEnd_3187935 := by exact prefixLift 3187935
  have htrace : WordTrace (prefixWord ++ tailWord_3187935) baseStart_3187935 baseEnd_3187935 := by
    simpa [prefixWord, tailWord_3187935, baseEnd_3187935] using wordTrace_append hprefix tailTrace_3187935
  have hstable : (prefixWord ++ tailWord_3187935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187935).length < 2 ^ (prefixWord ++ tailWord_3187935).sum := by decide
  have hdescent : baseEnd_3187935 < baseStart_3187935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187937 : List Nat := [1, 2, 3, 1, 3, 3, 1, 3, 5]
def baseStart_3187937 : Nat := 118140960795 + 3187937 * 2 ^ 59
def prefixEnd_3187937 : Nat := 4983230072969 + 3 ^ 40 * 3187937 * 2
def baseEnd_3187937 : Nat := 363765328278310870116989

theorem tailTrace_3187937 : CollatzResearch.WordTrace tailWord_3187937 prefixEnd_3187937 363765328278310870116989 := by
  unfold tailWord_3187937
  simp only [CollatzResearch.WordTrace]
  refine ⟨116273614651656180138330065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77515743101104120092220043 116273614651656180138330065)
  ·
    refine ⟨87205210988742135103747549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116273614651656180138330065 87205210988742135103747549)
    ·
      refine ⟨32701954120778300663905331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87205210988742135103747549 32701954120778300663905331)
      ·
        refine ⟨49052931181167450995857997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32701954120778300663905331 49052931181167450995857997)
        ·
          refine ⟨18394849192937794123446749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49052931181167450995857997 18394849192937794123446749)
          ·
            refine ⟨6898068447351672796292531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18394849192937794123446749 6898068447351672796292531)
            ·
              refine ⟨10347102671027509194438797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6898068447351672796292531 10347102671027509194438797)
              ·
                refine ⟨3880163501635315947914549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10347102671027509194438797 3880163501635315947914549)
                ·
                  refine ⟨363765328278310870116989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3880163501635315947914549 363765328278310870116989)
                  ·
                    rfl

theorem cell22_3187937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 5].length) (baseStart_3187937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187937 prefixEnd_3187937 := by exact prefixLift 3187937
  have htrace : WordTrace (prefixWord ++ tailWord_3187937) baseStart_3187937 baseEnd_3187937 := by
    simpa [prefixWord, tailWord_3187937, baseEnd_3187937] using wordTrace_append hprefix tailTrace_3187937
  have hstable : (prefixWord ++ tailWord_3187937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187937).length < 2 ^ (prefixWord ++ tailWord_3187937).sum := by decide
  have hdescent : baseEnd_3187937 < baseStart_3187937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187986 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_3187986 : Nat := 118140960795 + 3187986 * 2 ^ 59
def prefixEnd_3187986 : Nat := 4983230072969 + 3 ^ 40 * 3187986 * 2
def baseEnd_3187986 : Nat := 1091312758536312815875817

theorem tailTrace_3187986 : CollatzResearch.WordTrace tailWord_3187986 prefixEnd_3187986 1091312758536312815875817 := by
  unfold tailWord_3187986
  simp only [CollatzResearch.WordTrace]
  refine ⟨29068850457119665376715953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77516934552319107671242541 29068850457119665376715953)
  ·
    refine ⟨21801637842839749032536965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29068850457119665376715953 21801637842839749032536965)
    ·
      refine ⟨4087807095532452943600681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21801637842839749032536965 4087807095532452943600681)
      ·
        refine ⟨3065855321649339707700511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4087807095532452943600681 3065855321649339707700511)
        ·
          refine ⟨4598782982474009561550767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3065855321649339707700511 4598782982474009561550767)
          ·
            refine ⟨6898174473711014342326151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4598782982474009561550767 6898174473711014342326151)
            ·
              refine ⟨10347261710566521513489227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6898174473711014342326151 10347261710566521513489227)
              ·
                refine ⟨15520892565849782270233841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10347261710566521513489227 15520892565849782270233841)
                ·
                  refine ⟨11640669424387336702675381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15520892565849782270233841 11640669424387336702675381)
                  ·
                    refine ⟨1091312758536312815875817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11640669424387336702675381 1091312758536312815875817)
                    ·
                      rfl

theorem cell22_3187986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_3187986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187986 prefixEnd_3187986 := by exact prefixLift 3187986
  have htrace : WordTrace (prefixWord ++ tailWord_3187986) baseStart_3187986 baseEnd_3187986 := by
    simpa [prefixWord, tailWord_3187986, baseEnd_3187986] using wordTrace_append hprefix tailTrace_3187986
  have hstable : (prefixWord ++ tailWord_3187986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187986).length < 2 ^ (prefixWord ++ tailWord_3187986).sum := by decide
  have hdescent : baseEnd_3187986 < baseStart_3187986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187995 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 1, 6]
def baseStart_3187995 : Nat := 118140960795 + 3187995 * 2 ^ 59
def prefixEnd_3187995 : Nat := 4983230072969 + 3 ^ 40 * 3187995 * 2
def baseEnd_3187995 : Nat := 1091315839420239792400789

theorem tailTrace_3187995 : CollatzResearch.WordTrace tailWord_3187995 prefixEnd_3187995 1091315839420239792400789 := by
  unfold tailWord_3187995
  simp only [CollatzResearch.WordTrace]
  refine ⟨116275730085446056043941439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77517153390297370695960959 116275730085446056043941439)
  ·
    refine ⟨174413595128169084065912159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116275730085446056043941439 174413595128169084065912159)
    ·
      refine ⟨261620392692253626098868239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174413595128169084065912159 261620392692253626098868239)
      ·
        refine ⟨392430589038380439148302359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261620392692253626098868239 392430589038380439148302359)
        ·
          refine ⟨588645883557570658722453539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392430589038380439148302359 588645883557570658722453539)
          ·
            refine ⟨882968825336355988083680309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588645883557570658722453539 882968825336355988083680309)
            ·
              refine ⟨82778327375283373882845029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 882968825336355988083680309 82778327375283373882845029)
              ·
                refine ⟨15520936382865632603033443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82778327375283373882845029 15520936382865632603033443)
                ·
                  refine ⟨23281404574298448904550165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15520936382865632603033443 23281404574298448904550165)
                  ·
                    refine ⟨1091315839420239792400789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23281404574298448904550165 1091315839420239792400789)
                    ·
                      rfl

theorem cell22_3187995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 6].length) (baseStart_3187995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3187995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3187995 prefixEnd_3187995 := by exact prefixLift 3187995
  have htrace : WordTrace (prefixWord ++ tailWord_3187995) baseStart_3187995 baseEnd_3187995 := by
    simpa [prefixWord, tailWord_3187995, baseEnd_3187995] using wordTrace_append hprefix tailTrace_3187995
  have hstable : (prefixWord ++ tailWord_3187995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187995).length < 2 ^ (prefixWord ++ tailWord_3187995).sum := by decide
  have hdescent : baseEnd_3187995 < baseStart_3187995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188031 : List Nat := [1, 1, 2, 2, 4, 4, 1, 2, 2, 3]
def baseStart_3188031 : Nat := 118140960795 + 3188031 * 2 ^ 59
def prefixEnd_3188031 : Nat := 4983230072969 + 3 ^ 40 * 3188031 * 2
def baseEnd_3188031 : Nat := 1091328162955947698500679

theorem tailTrace_3188031 : CollatzResearch.WordTrace tailWord_3188031 prefixEnd_3188031 1091328162955947698500679 := by
  unfold tailWord_3188031
  simp only [CollatzResearch.WordTrace]
  refine ⟨116277043113315634192251947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77518028742210422794834631 116277043113315634192251947)
  ·
    refine ⟨174415564669973451288377921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116277043113315634192251947 174415564669973451288377921)
    ·
      refine ⟨130811673502480088466283441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174415564669973451288377921 130811673502480088466283441)
      ·
        refine ⟨98108755126860066349712581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130811673502480088466283441 98108755126860066349712581)
        ·
          refine ⟨18395391586286262440571109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98108755126860066349712581 18395391586286262440571109)
          ·
            refine ⟨3449135922428674207607083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18395391586286262440571109 3449135922428674207607083)
            ·
              refine ⟨5173703883643011311410625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3449135922428674207607083 5173703883643011311410625)
              ·
                refine ⟨3880277912732258483557969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5173703883643011311410625 3880277912732258483557969)
                ·
                  refine ⟨2910208434549193862668477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3880277912732258483557969 2910208434549193862668477)
                  ·
                    refine ⟨1091328162955947698500679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2910208434549193862668477 1091328162955947698500679)
                    ·
                      rfl

theorem cell22_3188031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 3].length) (baseStart_3188031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188031 prefixEnd_3188031 := by exact prefixLift 3188031
  have htrace : WordTrace (prefixWord ++ tailWord_3188031) baseStart_3188031 baseEnd_3188031 := by
    simpa [prefixWord, tailWord_3188031, baseEnd_3188031] using wordTrace_append hprefix tailTrace_3188031
  have hstable : (prefixWord ++ tailWord_3188031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188031).length < 2 ^ (prefixWord ++ tailWord_3188031).sum := by decide
  have hdescent : baseEnd_3188031 < baseStart_3188031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188093 : List Nat := [1, 4, 1, 1, 2, 2, 5, 2, 1, 3]
def baseStart_3188093 : Nat := 118140960795 + 3188093 * 2 ^ 59
def prefixEnd_3188093 : Nat := 4983230072969 + 3 ^ 40 * 3188093 * 2
def baseEnd_3188093 : Nat := 1091349386823000203450489

theorem tailTrace_3188093 : CollatzResearch.WordTrace tailWord_3188093 prefixEnd_3188093 1091349386823000203450489 := by
  unfold tailWord_3188093
  simp only [CollatzResearch.WordTrace]
  refine ⟨116279304439091018781008933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77519536292727345854005955 116279304439091018781008933)
  ·
    refine ⟨21802369582329566021439175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116279304439091018781008933 21802369582329566021439175)
    ·
      refine ⟨32703554373494349032158763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21802369582329566021439175 32703554373494349032158763)
      ·
        refine ⟨49055331560241523548238145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32703554373494349032158763 49055331560241523548238145)
        ·
          refine ⟨36791498670181142661178609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49055331560241523548238145 36791498670181142661178609)
          ·
            refine ⟨27593624002635856995883957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36791498670181142661178609 27593624002635856995883957)
            ·
              refine ⟨2586902250247111593364121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27593624002635856995883957 2586902250247111593364121)
              ·
                refine ⟨1940176687685333695023091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2586902250247111593364121 1940176687685333695023091)
                ·
                  refine ⟨2910265031528000542534637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1940176687685333695023091 2910265031528000542534637)
                  ·
                    refine ⟨1091349386823000203450489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2910265031528000542534637 1091349386823000203450489)
                    ·
                      rfl

theorem cell22_3188093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_3188093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188093 prefixEnd_3188093 := by exact prefixLift 3188093
  have htrace : WordTrace (prefixWord ++ tailWord_3188093) baseStart_3188093 baseEnd_3188093 := by
    simpa [prefixWord, tailWord_3188093, baseEnd_3188093] using wordTrace_append hprefix tailTrace_3188093
  have hstable : (prefixWord ++ tailWord_3188093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188093).length < 2 ^ (prefixWord ++ tailWord_3188093).sum := by decide
  have hdescent : baseEnd_3188093 < baseStart_3188093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188117 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 6]
def baseStart_3188117 : Nat := 118140960795 + 3188117 * 2 ^ 59
def prefixEnd_3188117 : Nat := 4983230072969 + 3 ^ 40 * 3188117 * 2
def baseEnd_3188117 : Nat := 363785867504490713616805

theorem tailTrace_3188117 : CollatzResearch.WordTrace tailWord_3188117 prefixEnd_3188117 363785867504490713616805 := by
  unfold tailWord_3188117
  simp only [CollatzResearch.WordTrace]
  refine ⟨116280179791004070879882605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77520119860669380586588403 116280179791004070879882605)
  ·
    refine ⟨43605067421626526579955977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116280179791004070879882605 43605067421626526579955977)
    ·
      refine ⟨32703800566219894934966983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43605067421626526579955977 32703800566219894934966983)
      ·
        refine ⟨49055700849329842402450475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32703800566219894934966983 49055700849329842402450475)
        ·
          refine ⟨73583551273994763603675713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49055700849329842402450475 73583551273994763603675713)
          ·
            refine ⟨55187663455496072702756785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73583551273994763603675713 55187663455496072702756785)
            ·
              refine ⟨41390747591622054527067589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55187663455496072702756785 41390747591622054527067589)
              ·
                refine ⟨7760765173429135223825173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41390747591622054527067589 7760765173429135223825173)
                ·
                  refine ⟨363785867504490713616805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7760765173429135223825173 363785867504490713616805)
                  ·
                    rfl

theorem cell22_3188117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_3188117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188117 prefixEnd_3188117 := by exact prefixLift 3188117
  have htrace : WordTrace (prefixWord ++ tailWord_3188117) baseStart_3188117 baseEnd_3188117 := by
    simpa [prefixWord, tailWord_3188117, baseEnd_3188117] using wordTrace_append hprefix tailTrace_3188117
  have hstable : (prefixWord ++ tailWord_3188117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188117).length < 2 ^ (prefixWord ++ tailWord_3188117).sum := by decide
  have hdescent : baseEnd_3188117 < baseStart_3188117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188192 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 1, 8]
def baseStart_3188192 : Nat := 118140960795 + 3188192 * 2 ^ 59
def prefixEnd_3188192 : Nat := 4983230072969 + 3 ^ 40 * 3188192 * 2
def baseEnd_3188192 : Nat := 1091383276546196945225185

theorem tailTrace_3188192 : CollatzResearch.WordTrace tailWord_3188192 prefixEnd_3188192 1091383276546196945225185 := by
  unfold tailWord_3188192
  simp only [CollatzResearch.WordTrace]
  refine ⟨58141457632866179344431415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77521943510488239125908553 58141457632866179344431415)
  ·
    refine ⟨87212186449299269016647123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58141457632866179344431415 87212186449299269016647123)
    ·
      refine ⟨130818279673948903524970685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87212186449299269016647123 130818279673948903524970685)
      ·
        refine ⟨49056854877730838821864007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130818279673948903524970685 49056854877730838821864007)
        ·
          refine ⟨73585282316596258232796011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49056854877730838821864007 73585282316596258232796011)
          ·
            refine ⟨110377923474894387349194017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73585282316596258232796011 110377923474894387349194017)
            ·
              refine ⟨82783442606170790511895513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110377923474894387349194017 82783442606170790511895513)
              ·
                refine ⟨62087581954628092883921635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82783442606170790511895513 62087581954628092883921635)
                ·
                  refine ⟨93131372931942139325882453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62087581954628092883921635 93131372931942139325882453)
                  ·
                    refine ⟨1091383276546196945225185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93131372931942139325882453 1091383276546196945225185)
                    ·
                      rfl

theorem cell22_3188192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_3188192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188192 prefixEnd_3188192 := by exact prefixLift 3188192
  have htrace : WordTrace (prefixWord ++ tailWord_3188192) baseStart_3188192 baseEnd_3188192 := by
    simpa [prefixWord, tailWord_3188192, baseEnd_3188192] using wordTrace_append hprefix tailTrace_3188192
  have hstable : (prefixWord ++ tailWord_3188192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188192).length < 2 ^ (prefixWord ++ tailWord_3188192).sum := by decide
  have hdescent : baseEnd_3188192 < baseStart_3188192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188230 : List Nat := [6, 2, 1, 1, 2, 1, 1, 8]
def baseStart_3188230 : Nat := 118140960795 + 3188230 * 2 ^ 59
def prefixEnd_3188230 : Nat := 4983230072969 + 3 ^ 40 * 3188230 * 2
def baseEnd_3188230 : Nat := 121266253858086390308341

theorem tailTrace_3188230 : CollatzResearch.WordTrace tailWord_3188230 prefixEnd_3188230 121266253858086390308341 := by
  unfold tailWord_3188230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3633884413737334099335817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77522867493063127452497429 3633884413737334099335817)
  ·
    refine ⟨2725413310303000574501863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3633884413737334099335817 2725413310303000574501863)
    ·
      refine ⟨4088119965454500861752795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2725413310303000574501863 4088119965454500861752795)
      ·
        refine ⟨6132179948181751292629193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4088119965454500861752795 6132179948181751292629193)
        ·
          refine ⟨4599134961136313469471895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6132179948181751292629193 4599134961136313469471895)
          ·
            refine ⟨6898702441704470204207843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4599134961136313469471895 6898702441704470204207843)
            ·
              refine ⟨10348053662556705306311765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6898702441704470204207843 10348053662556705306311765)
              ·
                refine ⟨121266253858086390308341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10348053662556705306311765 121266253858086390308341)
                ·
                  rfl

theorem cell22_3188230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_3188230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188230 prefixEnd_3188230 := by exact prefixLift 3188230
  have htrace : WordTrace (prefixWord ++ tailWord_3188230) baseStart_3188230 baseEnd_3188230 := by
    simpa [prefixWord, tailWord_3188230, baseEnd_3188230] using wordTrace_append hprefix tailTrace_3188230
  have hstable : (prefixWord ++ tailWord_3188230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188230).length < 2 ^ (prefixWord ++ tailWord_3188230).sum := by decide
  have hdescent : baseEnd_3188230 < baseStart_3188230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188245 : List Nat := [1, 3, 2, 1, 3, 4, 1, 3, 1, 3]
def baseStart_3188245 : Nat := 118140960795 + 3188245 * 2 ^ 59
def prefixEnd_3188245 : Nat := 4983230072969 + 3 ^ 40 * 3188245 * 2
def baseEnd_3188245 : Nat := 1091401419529322473650023

theorem tailTrace_3188245 : CollatzResearch.WordTrace tailWord_3188245 prefixEnd_3188245 1091401419529322473650023 := by
  unfold tailWord_3188245
  simp only [CollatzResearch.WordTrace]
  refine ⟨116284848334540348740542189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77523232223026899160361459 116284848334540348740542189)
  ·
    refine ⟨43606818125452630777703321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116284848334540348740542189 43606818125452630777703321)
    ·
      refine ⟨32705113594089473083277491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43606818125452630777703321 32705113594089473083277491)
      ·
        refine ⟨49057670391134209624916237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32705113594089473083277491 49057670391134209624916237)
        ·
          refine ⟨18396626396675328609343589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49057670391134209624916237 18396626396675328609343589)
          ·
            refine ⟨3449367449376624114251923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18396626396675328609343589 3449367449376624114251923)
            ·
              refine ⟨5174051174064936171377885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3449367449376624114251923 5174051174064936171377885)
              ·
                refine ⟨1940269190274351064266707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5174051174064936171377885 1940269190274351064266707)
                ·
                  refine ⟨2910403785411526596400061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1940269190274351064266707 2910403785411526596400061)
                  ·
                    refine ⟨1091401419529322473650023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2910403785411526596400061 1091401419529322473650023)
                    ·
                      rfl

theorem cell22_3188245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_3188245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188245 prefixEnd_3188245 := by exact prefixLift 3188245
  have htrace : WordTrace (prefixWord ++ tailWord_3188245) baseStart_3188245 baseEnd_3188245 := by
    simpa [prefixWord, tailWord_3188245, baseEnd_3188245] using wordTrace_append hprefix tailTrace_3188245
  have hstable : (prefixWord ++ tailWord_3188245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188245).length < 2 ^ (prefixWord ++ tailWord_3188245).sum := by decide
  have hdescent : baseEnd_3188245 < baseStart_3188245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188376 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 7]
def baseStart_3188376 : Nat := 118140960795 + 3188376 * 2 ^ 59
def prefixEnd_3188376 : Nat := 4983230072969 + 3 ^ 40 * 3188376 * 2
def baseEnd_3188376 : Nat := 363815421168827266208207

theorem tailTrace_3188376 : CollatzResearch.WordTrace tailWord_3188376 prefixEnd_3188376 363815421168827266208207 := by
  unfold tailWord_3188376
  simp only [CollatzResearch.WordTrace]
  refine ⟨58144813148532879056780491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77526417531377172075707321 58144813148532879056780491)
  ·
    refine ⟨87217219722799318585170737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58144813148532879056780491 87217219722799318585170737)
    ·
      refine ⟨65412914792099488938878053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87217219722799318585170737 65412914792099488938878053)
      ·
        refine ⟨12264921523518654176039635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65412914792099488938878053 12264921523518654176039635)
        ·
          refine ⟨18397382285277981264059453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12264921523518654176039635 18397382285277981264059453)
          ·
            refine ⟨6899018356979242974022295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18397382285277981264059453 6899018356979242974022295)
            ·
              refine ⟨10348527535468864461033443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6899018356979242974022295 10348527535468864461033443)
              ·
                refine ⟨15522791303203296691550165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10348527535468864461033443 15522791303203296691550165)
                ·
                  refine ⟨363815421168827266208207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15522791303203296691550165 363815421168827266208207)
                  ·
                    rfl

theorem cell22_3188376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 7].length) (baseStart_3188376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188376 prefixEnd_3188376 := by exact prefixLift 3188376
  have htrace : WordTrace (prefixWord ++ tailWord_3188376) baseStart_3188376 baseEnd_3188376 := by
    simpa [prefixWord, tailWord_3188376, baseEnd_3188376] using wordTrace_append hprefix tailTrace_3188376
  have hstable : (prefixWord ++ tailWord_3188376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188376).length < 2 ^ (prefixWord ++ tailWord_3188376).sum := by decide
  have hdescent : baseEnd_3188376 < baseStart_3188376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188380 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 3, 3]
def baseStart_3188380 : Nat := 118140960795 + 3188380 * 2 ^ 59
def prefixEnd_3188380 : Nat := 4983230072969 + 3 ^ 40 * 3188380 * 2
def baseEnd_3188380 : Nat := 1091447632788227121524609

theorem tailTrace_3188380 : CollatzResearch.WordTrace tailWord_3188380 prefixEnd_3188380 1091447632788227121524609 := by
  unfold tailWord_3188380
  simp only [CollatzResearch.WordTrace]
  refine ⟨58144886094525633398353297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77526514792700844531137729 58144886094525633398353297)
  ·
    refine ⟨43608664570894225048764973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58144886094525633398353297 43608664570894225048764973)
    ·
      refine ⟨16353249214085334393286865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43608664570894225048764973 16353249214085334393286865)
      ·
        refine ⟨12264936910564000794965149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16353249214085334393286865 12264936910564000794965149)
        ·
          refine ⟨4599351341461500298111931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12264936910564000794965149 4599351341461500298111931)
          ·
            refine ⟨6899027012192250447167897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4599351341461500298111931 6899027012192250447167897)
            ·
              refine ⟨5174270259144187835375923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6899027012192250447167897 5174270259144187835375923)
              ·
                refine ⟨7761405388716281753063885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5174270259144187835375923 7761405388716281753063885)
                ·
                  refine ⟨2910527020768605657398957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7761405388716281753063885 2910527020768605657398957)
                  ·
                    refine ⟨1091447632788227121524609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2910527020768605657398957 1091447632788227121524609)
                    ·
                      rfl

theorem cell22_3188380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_3188380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188380 prefixEnd_3188380 := by exact prefixLift 3188380
  have htrace : WordTrace (prefixWord ++ tailWord_3188380) baseStart_3188380 baseEnd_3188380 := by
    simpa [prefixWord, tailWord_3188380, baseEnd_3188380] using wordTrace_append hprefix tailTrace_3188380
  have hstable : (prefixWord ++ tailWord_3188380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188380).length < 2 ^ (prefixWord ++ tailWord_3188380).sum := by decide
  have hdescent : baseEnd_3188380 < baseStart_3188380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188444 : List Nat := [2, 2, 5, 1, 3, 1, 2, 1, 5]
def baseStart_3188444 : Nat := 118140960795 + 3188444 * 2 ^ 59
def prefixEnd_3188444 : Nat := 4983230072969 + 3 ^ 40 * 3188444 * 2
def baseEnd_3188444 : Nat := 363823180432050762641471

theorem tailTrace_3188444 : CollatzResearch.WordTrace tailWord_3188444 prefixEnd_3188444 363823180432050762641471 := by
  unfold tailWord_3188444
  simp only [CollatzResearch.WordTrace]
  refine ⟨58146053230409702863518193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77528070973879603818024257 58146053230409702863518193)
  ·
    refine ⟨43609539922807277147638645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58146053230409702863518193 43609539922807277147638645)
    ·
      refine ⟨4088394367763182232591123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43609539922807277147638645 4088394367763182232591123)
      ·
        refine ⟨6132591551644773348886685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4088394367763182232591123 6132591551644773348886685)
        ·
          refine ⟨2299721831866790005832507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6132591551644773348886685 2299721831866790005832507)
          ·
            refine ⟨3449582747800185008748761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2299721831866790005832507 3449582747800185008748761)
            ·
              refine ⟨2587187060850138756561571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3449582747800185008748761 2587187060850138756561571)
              ·
                refine ⟨3880780591275208134842357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2587187060850138756561571 3880780591275208134842357)
                ·
                  refine ⟨363823180432050762641471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3880780591275208134842357 363823180432050762641471)
                  ·
                    rfl

theorem cell22_3188444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_3188444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188444 prefixEnd_3188444 := by exact prefixLift 3188444
  have htrace : WordTrace (prefixWord ++ tailWord_3188444) baseStart_3188444 baseEnd_3188444 := by
    simpa [prefixWord, tailWord_3188444, baseEnd_3188444] using wordTrace_append hprefix tailTrace_3188444
  have hstable : (prefixWord ++ tailWord_3188444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188444).length < 2 ^ (prefixWord ++ tailWord_3188444).sum := by decide
  have hdescent : baseEnd_3188444 < baseStart_3188444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188466 : List Nat := [3, 2, 1, 3, 1, 1, 1, 10]
def baseStart_3188466 : Nat := 118140960795 + 3188466 * 2 ^ 59
def prefixEnd_3188466 : Nat := 4983230072969 + 3 ^ 40 * 3188466 * 2
def baseEnd_3188466 : Nat := 121275230260639062652705

theorem tailTrace_3188466 : CollatzResearch.WordTrace tailWord_3188466 prefixEnd_3188466 121275230260639062652705 := by
  unfold tailWord_3188466
  simp only [CollatzResearch.WordTrace]
  refine ⟨29073227216684925871084313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77528605911159802322891501 29073227216684925871084313)
  ·
    refine ⟨21804920412513694403313235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29073227216684925871084313 21804920412513694403313235)
    ·
      refine ⟨32707380618770541604969853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21804920412513694403313235 32707380618770541604969853)
      ·
        refine ⟨12265267732038953101863695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32707380618770541604969853 12265267732038953101863695)
        ·
          refine ⟨18397901598058429652795543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12265267732038953101863695 18397901598058429652795543)
          ·
            refine ⟨27596852397087644479193315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18397901598058429652795543 27596852397087644479193315)
            ·
              refine ⟨41395278595631466718789973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27596852397087644479193315 41395278595631466718789973)
              ·
                refine ⟨121275230260639062652705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41395278595631466718789973 121275230260639062652705)
                ·
                  rfl

theorem cell22_3188466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_3188466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188466 prefixEnd_3188466 := by exact prefixLift 3188466
  have htrace : WordTrace (prefixWord ++ tailWord_3188466) baseStart_3188466 baseEnd_3188466 := by
    simpa [prefixWord, tailWord_3188466, baseEnd_3188466] using wordTrace_append hprefix tailTrace_3188466
  have hstable : (prefixWord ++ tailWord_3188466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188466).length < 2 ^ (prefixWord ++ tailWord_3188466).sum := by decide
  have hdescent : baseEnd_3188466 < baseStart_3188466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188487 : List Nat := [1, 1, 4, 4, 2, 1, 2, 2, 2, 3]
def baseStart_3188487 : Nat := 118140960795 + 3188487 * 2 ^ 59
def prefixEnd_3188487 : Nat := 4983230072969 + 3 ^ 40 * 3188487 * 2
def baseEnd_3188487 : Nat := 1091484261074914509099281

theorem tailTrace_3188487 : CollatzResearch.WordTrace tailWord_3188487 prefixEnd_3188487 1091484261074914509099281 := by
  unfold tailWord_3188487
  simp only [CollatzResearch.WordTrace]
  refine ⟨116293674799663624070851715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77529116533109082713901143 116293674799663624070851715)
  ·
    refine ⟨174440512199495436106277573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116293674799663624070851715 174440512199495436106277573)
    ·
      refine ⟨32707596037405394269927045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174440512199495436106277573 32707596037405394269927045)
      ·
        refine ⟨6132674257013511425611321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32707596037405394269927045 6132674257013511425611321)
        ·
          refine ⟨4599505692760133569208491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6132674257013511425611321 4599505692760133569208491)
          ·
            refine ⟨6899258539140200353812737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4599505692760133569208491 6899258539140200353812737)
            ·
              refine ⟨5174443904355150265359553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6899258539140200353812737 5174443904355150265359553)
              ·
                refine ⟨3880832928266362699019665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5174443904355150265359553 3880832928266362699019665)
                ·
                  refine ⟨2910624696199772024264749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3880832928266362699019665 2910624696199772024264749)
                  ·
                    refine ⟨1091484261074914509099281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2910624696199772024264749 1091484261074914509099281)
                    ·
                      rfl

theorem cell22_3188487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_3188487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188487 prefixEnd_3188487 := by exact prefixLift 3188487
  have htrace : WordTrace (prefixWord ++ tailWord_3188487) baseStart_3188487 baseEnd_3188487 := by
    simpa [prefixWord, tailWord_3188487, baseEnd_3188487] using wordTrace_append hprefix tailTrace_3188487
  have hstable : (prefixWord ++ tailWord_3188487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188487).length < 2 ^ (prefixWord ++ tailWord_3188487).sum := by decide
  have hdescent : baseEnd_3188487 < baseStart_3188487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188575 : List Nat := [1, 1, 2, 3, 1, 5, 2, 2, 1, 4]
def baseStart_3188575 : Nat := 118140960795 + 3188575 * 2 ^ 59
def prefixEnd_3188575 : Nat := 4983230072969 + 3 ^ 40 * 3188575 * 2
def baseEnd_3188575 : Nat := 1091514385273311612899011

theorem tailTrace_3188575 : CollatzResearch.WordTrace tailWord_3188575 prefixEnd_3188575 1091514385273311612899011 := by
  unfold tailWord_3188575
  simp only [CollatzResearch.WordTrace]
  refine ⟨116296884423344815100055179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77531256282229876733370119 116296884423344815100055179)
  ·
    refine ⟨174445326635017222650082769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116296884423344815100055179 174445326635017222650082769)
    ·
      refine ⟨130833994976262916987562077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174445326635017222650082769 130833994976262916987562077)
      ·
        refine ⟨49062748116098593870335779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130833994976262916987562077 49062748116098593870335779)
        ·
          refine ⟨73594122174147890805503669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49062748116098593870335779 73594122174147890805503669)
          ·
            refine ⟨6899448953826364763015969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73594122174147890805503669 6899448953826364763015969)
            ·
              refine ⟨5174586715369773572261977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6899448953826364763015969 5174586715369773572261977)
              ·
                refine ⟨3880940036527330179196483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5174586715369773572261977 3880940036527330179196483)
                ·
                  refine ⟨5821410054790995268794725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3880940036527330179196483 5821410054790995268794725)
                  ·
                    refine ⟨1091514385273311612899011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5821410054790995268794725 1091514385273311612899011)
                    ·
                      rfl

theorem cell22_3188575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_3188575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188575 prefixEnd_3188575 := by exact prefixLift 3188575
  have htrace : WordTrace (prefixWord ++ tailWord_3188575) baseStart_3188575 baseEnd_3188575 := by
    simpa [prefixWord, tailWord_3188575, baseEnd_3188575] using wordTrace_append hprefix tailTrace_3188575
  have hstable : (prefixWord ++ tailWord_3188575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188575).length < 2 ^ (prefixWord ++ tailWord_3188575).sum := by decide
  have hdescent : baseEnd_3188575 < baseStart_3188575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188605 : List Nat := [1, 4, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_3188605 : Nat := 118140960795 + 3188605 * 2 ^ 59
def prefixEnd_3188605 : Nat := 4983230072969 + 3 ^ 40 * 3188605 * 2
def baseEnd_3188605 : Nat := 1091524654886401534648919

theorem tailTrace_3188605 : CollatzResearch.WordTrace tailWord_3188605 prefixEnd_3188605 1091524654886401534648919 := by
  unfold tailWord_3188605
  simp only [CollatzResearch.WordTrace]
  refine ⟨116297978613236130223647269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77531985742157420149098179 116297978613236130223647269)
  ·
    refine ⟨21805870989981774416933863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116297978613236130223647269 21805870989981774416933863)
    ·
      refine ⟨32708806484972661625400795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21805870989981774416933863 32708806484972661625400795)
      ·
        refine ⟨49063209727458992438101193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32708806484972661625400795 49063209727458992438101193)
        ·
          refine ⟨36797407295594244328575895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49063209727458992438101193 36797407295594244328575895)
          ·
            refine ⟨55196110943391366492863843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36797407295594244328575895 55196110943391366492863843)
            ·
              refine ⟨82794166415087049739295765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55196110943391366492863843 82794166415087049739295765)
              ·
                refine ⟨3880976550707205456529489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82794166415087049739295765 3880976550707205456529489)
                ·
                  refine ⟨2910732413030404092397117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3880976550707205456529489 2910732413030404092397117)
                  ·
                    refine ⟨1091524654886401534648919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2910732413030404092397117 1091524654886401534648919)
                    ·
                      rfl

theorem cell22_3188605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_3188605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188605 prefixEnd_3188605 := by exact prefixLift 3188605
  have htrace : WordTrace (prefixWord ++ tailWord_3188605) baseStart_3188605 baseEnd_3188605 := by
    simpa [prefixWord, tailWord_3188605, baseEnd_3188605] using wordTrace_append hprefix tailTrace_3188605
  have hstable : (prefixWord ++ tailWord_3188605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188605).length < 2 ^ (prefixWord ++ tailWord_3188605).sum := by decide
  have hdescent : baseEnd_3188605 < baseStart_3188605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188680 : List Nat := [2, 1, 3, 1, 4, 1, 2, 3, 5]
def baseStart_3188680 : Nat := 118140960795 + 3188680 * 2 ^ 59
def prefixEnd_3188680 : Nat := 4983230072969 + 3 ^ 40 * 3188680 * 2
def baseEnd_3188680 : Nat := 363850109639708779674563

theorem tailTrace_3188680 : CollatzResearch.WordTrace tailWord_3188680 prefixEnd_3188680 363850109639708779674563 := by
  unfold tailWord_3188680
  simp only [CollatzResearch.WordTrace]
  refine ⟨58150357043982209016313747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77533809391976278688418329 58150357043982209016313747)
  ·
    refine ⟨87225535565973313524470621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58150357043982209016313747 87225535565973313524470621)
    ·
      refine ⟨32709575837239992571676483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87225535565973313524470621 32709575837239992571676483)
      ·
        refine ⟨49064363755859988857514725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32709575837239992571676483 49064363755859988857514725)
        ·
          refine ⟨9199568204223747910784011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49064363755859988857514725 9199568204223747910784011)
          ·
            refine ⟨13799352306335621866176017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9199568204223747910784011 13799352306335621866176017)
            ·
              refine ⟨10349514229751716399632013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13799352306335621866176017 10349514229751716399632013)
              ·
                refine ⟨3881067836156893649862005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10349514229751716399632013 3881067836156893649862005)
                ·
                  refine ⟨363850109639708779674563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3881067836156893649862005 363850109639708779674563)
                  ·
                    rfl

theorem cell22_3188680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 5].length) (baseStart_3188680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188680 prefixEnd_3188680 := by exact prefixLift 3188680
  have htrace : WordTrace (prefixWord ++ tailWord_3188680) baseStart_3188680 baseEnd_3188680 := by
    simpa [prefixWord, tailWord_3188680, baseEnd_3188680] using wordTrace_append hprefix tailTrace_3188680
  have hstable : (prefixWord ++ tailWord_3188680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188680).length < 2 ^ (prefixWord ++ tailWord_3188680).sum := by decide
  have hdescent : baseEnd_3188680 < baseStart_3188680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188701 : List Nat := [1, 4, 3, 1, 3, 1, 2, 3, 1, 3]
def baseStart_3188701 : Nat := 118140960795 + 3188701 * 2 ^ 59
def prefixEnd_3188701 : Nat := 4983230072969 + 3 ^ 40 * 3188701 * 2
def baseEnd_3188701 : Nat := 1091557517648289284248625

theorem tailTrace_3188701 : CollatzResearch.WordTrace tailWord_3188701 prefixEnd_3188701 1091557517648289284248625 := by
  unfold tailWord_3188701
  simp only [CollatzResearch.WordTrace]
  refine ⟨116301480020888338619141957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77534320013925559079427971 116301480020888338619141957)
  ·
    refine ⟨21806527503916563491089117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116301480020888338619141957 21806527503916563491089117)
    ·
      refine ⟨8177447813968711309158419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21806527503916563491089117 8177447813968711309158419)
      ·
        refine ⟨12266171720953066963737629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8177447813968711309158419 12266171720953066963737629)
        ·
          refine ⟨4599814395357400111401611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12266171720953066963737629 4599814395357400111401611)
          ·
            refine ⟨6899721593036100167102417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4599814395357400111401611 6899721593036100167102417)
            ·
              refine ⟨5174791194777075125326813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6899721593036100167102417 5174791194777075125326813)
              ·
                refine ⟨1940546698041403171997555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5174791194777075125326813 1940546698041403171997555)
                ·
                  refine ⟨2910820047062104757996333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1940546698041403171997555 2910820047062104757996333)
                  ·
                    refine ⟨1091557517648289284248625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2910820047062104757996333 1091557517648289284248625)
                    ·
                      rfl

theorem cell22_3188701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_3188701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188701 prefixEnd_3188701 := by exact prefixLift 3188701
  have htrace : WordTrace (prefixWord ++ tailWord_3188701) baseStart_3188701 baseEnd_3188701 := by
    simpa [prefixWord, tailWord_3188701, baseEnd_3188701] using wordTrace_append hprefix tailTrace_3188701
  have hstable : (prefixWord ++ tailWord_3188701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188701).length < 2 ^ (prefixWord ++ tailWord_3188701).sum := by decide
  have hdescent : baseEnd_3188701 < baseStart_3188701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188708 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 8]
def baseStart_3188708 : Nat := 118140960795 + 3188708 * 2 ^ 59
def prefixEnd_3188708 : Nat := 4983230072969 + 3 ^ 40 * 3188708 * 2
def baseEnd_3188708 : Nat := 363853304630447866441201

theorem tailTrace_3188708 : CollatzResearch.WordTrace tailWord_3188708 prefixEnd_3188708 363853304630447866441201 := by
  unfold tailWord_3188708
  simp only [CollatzResearch.WordTrace]
  refine ⟨58150867665931489407323389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77534490221241985876431185 58150867665931489407323389)
  ·
    refine ⟨21806575374724308527746271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58150867665931489407323389 21806575374724308527746271)
    ·
      refine ⟨32709863062086462791619407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21806575374724308527746271 32709863062086462791619407)
      ·
        refine ⟨49064794593129694187429111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32709863062086462791619407 49064794593129694187429111)
        ·
          refine ⟨73597191889694541281143667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49064794593129694187429111 73597191889694541281143667)
          ·
            refine ⟨110395787834541811921715501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73597191889694541281143667 110395787834541811921715501)
            ·
              refine ⟨41398420437953179470643313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110395787834541811921715501 41398420437953179470643313)
              ·
                refine ⟨31048815328464884602982485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41398420437953179470643313 31048815328464884602982485)
                ·
                  refine ⟨363853304630447866441201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31048815328464884602982485 363853304630447866441201)
                  ·
                    rfl

theorem cell22_3188708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_3188708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188708 prefixEnd_3188708 := by exact prefixLift 3188708
  have htrace : WordTrace (prefixWord ++ tailWord_3188708) baseStart_3188708 baseEnd_3188708 := by
    simpa [prefixWord, tailWord_3188708, baseEnd_3188708] using wordTrace_append hprefix tailTrace_3188708
  have hstable : (prefixWord ++ tailWord_3188708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188708).length < 2 ^ (prefixWord ++ tailWord_3188708).sum := by decide
  have hdescent : baseEnd_3188708 < baseStart_3188708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188723 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 3, 5]
def baseStart_3188723 : Nat := 118140960795 + 3188723 * 2 ^ 59
def prefixEnd_3188723 : Nat := 4983230072969 + 3 ^ 40 * 3188723 * 2
def baseEnd_3188723 : Nat := 1091565048697888560198557

theorem tailTrace_3188723 : CollatzResearch.WordTrace tailWord_3188723 prefixEnd_3188723 1091565048697888560198557 := by
  unfold tailWord_3188723
  simp only [CollatzResearch.WordTrace]
  refine ⟨116302282426808636376442823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77534854951205757584295215 116302282426808636376442823)
  ·
    refine ⟨174453423640212954564664235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116302282426808636376442823 174453423640212954564664235)
    ·
      refine ⟨261680135460319431846996353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174453423640212954564664235 261680135460319431846996353)
      ·
        refine ⟨196260101595239573885247265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261680135460319431846996353 196260101595239573885247265)
        ·
          refine ⟨147195076196429680413935449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196260101595239573885247265 147195076196429680413935449)
          ·
            refine ⟨110396307147322260310451587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147195076196429680413935449 110396307147322260310451587)
            ·
              refine ⟨165594460720983390465677381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110396307147322260310451587 165594460720983390465677381)
              ·
                refine ⟨31048961385184385712314509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165594460720983390465677381 31048961385184385712314509)
                ·
                  refine ⟨11643360519444144642117941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31048961385184385712314509 11643360519444144642117941)
                  ·
                    refine ⟨1091565048697888560198557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11643360519444144642117941 1091565048697888560198557)
                    ·
                      rfl

theorem cell22_3188723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 5].length) (baseStart_3188723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188723 prefixEnd_3188723 := by exact prefixLift 3188723
  have htrace : WordTrace (prefixWord ++ tailWord_3188723) baseStart_3188723 baseEnd_3188723 := by
    simpa [prefixWord, tailWord_3188723, baseEnd_3188723] using wordTrace_append hprefix tailTrace_3188723
  have hstable : (prefixWord ++ tailWord_3188723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188723).length < 2 ^ (prefixWord ++ tailWord_3188723).sum := by decide
  have hdescent : baseEnd_3188723 < baseStart_3188723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188776 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 6]
def baseStart_3188776 : Nat := 118140960795 + 3188776 * 2 ^ 59
def prefixEnd_3188776 : Nat := 4983230072969 + 3 ^ 40 * 3188776 * 2
def baseEnd_3188776 : Nat := 363861063893671362874465

theorem tailTrace_3188776 : CollatzResearch.WordTrace tailWord_3188776 prefixEnd_3188776 363861063893671362874465 := by
  unfold tailWord_3188776
  simp only [CollatzResearch.WordTrace]
  refine ⟨58152107747808313214061091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77536143663744417618748121 58152107747808313214061091)
  ·
    refine ⟨87228161621712469821091637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58152107747808313214061091 87228161621712469821091637)
    ·
      refine ⟨8177640152035544045727341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87228161621712469821091637 8177640152035544045727341)
      ·
        refine ⟨3066615057013329017147753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8177640152035544045727341 3066615057013329017147753)
        ·
          refine ⟨2299961292759996762860815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3066615057013329017147753 2299961292759996762860815)
          ·
            refine ⟨3449941939139995144291223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2299961292759996762860815 3449941939139995144291223)
            ·
              refine ⟨5174912908709992716436835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3449941939139995144291223 5174912908709992716436835)
              ·
                refine ⟨7762369363064989074655253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5174912908709992716436835 7762369363064989074655253)
                ·
                  refine ⟨363861063893671362874465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7762369363064989074655253 363861063893671362874465)
                  ·
                    rfl

theorem cell22_3188776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 6].length) (baseStart_3188776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188776 prefixEnd_3188776 := by exact prefixLift 3188776
  have htrace : WordTrace (prefixWord ++ tailWord_3188776) baseStart_3188776 baseEnd_3188776 := by
    simpa [prefixWord, tailWord_3188776, baseEnd_3188776] using wordTrace_append hprefix tailTrace_3188776
  have hstable : (prefixWord ++ tailWord_3188776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188776).length < 2 ^ (prefixWord ++ tailWord_3188776).sum := by decide
  have hdescent : baseEnd_3188776 < baseStart_3188776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188832 : List Nat := [2, 1, 1, 3, 2, 4, 2, 2, 5]
def baseStart_3188832 : Nat := 118140960795 + 3188832 * 2 ^ 59
def prefixEnd_3188832 : Nat := 4983230072969 + 3 ^ 40 * 3188832 * 2
def baseEnd_3188832 : Nat := 363867453875149536407741

theorem tailTrace_3188832 : CollatzResearch.WordTrace tailWord_3188832 prefixEnd_3188832 363867453875149536407741 := by
  unfold tailWord_3188832
  simp only [CollatzResearch.WordTrace]
  refine ⟨58153128991706873996080375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77537505322275831994773833 58153128991706873996080375)
  ·
    refine ⟨87229693487560310994120563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58153128991706873996080375 87229693487560310994120563)
    ·
      refine ⟨130844540231340466491180845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87229693487560310994120563 130844540231340466491180845)
      ·
        refine ⟨49066702586752674934192817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130844540231340466491180845 49066702586752674934192817)
        ·
          refine ⟨36800026940064506200644613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49066702586752674934192817 36800026940064506200644613)
          ·
            refine ⟨6900005051262094912620865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36800026940064506200644613 6900005051262094912620865)
            ·
              refine ⟨5175003788446571184465649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6900005051262094912620865 5175003788446571184465649)
              ·
                refine ⟨3881252841334928388349237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5175003788446571184465649 3881252841334928388349237)
                ·
                  refine ⟨363867453875149536407741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3881252841334928388349237 363867453875149536407741)
                  ·
                    rfl

theorem cell22_3188832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 5].length) (baseStart_3188832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188832 prefixEnd_3188832 := by exact prefixLift 3188832
  have htrace : WordTrace (prefixWord ++ tailWord_3188832) baseStart_3188832 baseEnd_3188832 := by
    simpa [prefixWord, tailWord_3188832, baseEnd_3188832] using wordTrace_append hprefix tailTrace_3188832
  have hstable : (prefixWord ++ tailWord_3188832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188832).length < 2 ^ (prefixWord ++ tailWord_3188832).sum := by decide
  have hdescent : baseEnd_3188832 < baseStart_3188832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188836 : List Nat := [2, 3, 1, 1, 2, 1, 6, 2, 1, 3]
def baseStart_3188836 : Nat := 118140960795 + 3188836 * 2 ^ 59
def prefixEnd_3188836 : Nat := 4983230072969 + 3 ^ 40 * 3188836 * 2
def baseEnd_3188836 : Nat := 1091603730907193932123211

theorem tailTrace_3188836 : CollatzResearch.WordTrace tailWord_3188836 prefixEnd_3188836 1091603730907193932123211 := by
  unfold tailWord_3188836
  simp only [CollatzResearch.WordTrace]
  refine ⟨58153201937699628337653181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77537602583599504450204241 58153201937699628337653181)
  ·
    refine ⟨21807450726637360626619943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58153201937699628337653181 21807450726637360626619943)
    ·
      refine ⟨32711176089956040939929915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21807450726637360626619943 32711176089956040939929915)
      ·
        refine ⟨49066764134934061409894873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32711176089956040939929915 49066764134934061409894873)
        ·
          refine ⟨36800073101200546057421155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49066764134934061409894873 36800073101200546057421155)
          ·
            refine ⟨55200109651800819086131733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36800073101200546057421155 55200109651800819086131733)
            ·
              refine ⟨2587505139928163394662425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55200109651800819086131733 2587505139928163394662425)
              ·
                refine ⟨1940628854946122545996819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2587505139928163394662425 1940628854946122545996819)
                ·
                  refine ⟨2910943282419183818995229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1940628854946122545996819 2910943282419183818995229)
                  ·
                    refine ⟨1091603730907193932123211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2910943282419183818995229 1091603730907193932123211)
                    ·
                      rfl

theorem cell22_3188836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_3188836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188836 prefixEnd_3188836 := by exact prefixLift 3188836
  have htrace : WordTrace (prefixWord ++ tailWord_3188836) baseStart_3188836 baseEnd_3188836 := by
    simpa [prefixWord, tailWord_3188836, baseEnd_3188836] using wordTrace_append hprefix tailTrace_3188836
  have hstable : (prefixWord ++ tailWord_3188836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188836).length < 2 ^ (prefixWord ++ tailWord_3188836).sum := by decide
  have hdescent : baseEnd_3188836 < baseStart_3188836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188860 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 8]
def baseStart_3188860 : Nat := 118140960795 + 3188860 * 2 ^ 59
def prefixEnd_3188860 : Nat := 4983230072969 + 3 ^ 40 * 3188860 * 2
def baseEnd_3188860 : Nat := 363870648865888623174379

theorem tailTrace_3188860 : CollatzResearch.WordTrace tailWord_3188860 prefixEnd_3188860 363870648865888623174379 := by
  unfold tailWord_3188860
  simp only [CollatzResearch.WordTrace]
  refine ⟨58153639613656154387090017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77538186151541539182786689 58153639613656154387090017)
  ·
    refine ⟨43615229710242115790317513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58153639613656154387090017 43615229710242115790317513)
    ·
      refine ⟨32711422282681586842738135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43615229710242115790317513 32711422282681586842738135)
      ·
        refine ⟨49067133424022380264107203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32711422282681586842738135 49067133424022380264107203)
        ·
          refine ⟨73600700136033570396160805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49067133424022380264107203 73600700136033570396160805)
          ·
            refine ⟨13800131275506294449280151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73600700136033570396160805 13800131275506294449280151)
            ·
              refine ⟨20700196913259441673920227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13800131275506294449280151 20700196913259441673920227)
              ·
                refine ⟨31050295369889162510880341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20700196913259441673920227 31050295369889162510880341)
                ·
                  refine ⟨363870648865888623174379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31050295369889162510880341 363870648865888623174379)
                  ·
                    rfl

theorem cell22_3188860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_3188860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188860 prefixEnd_3188860 := by exact prefixLift 3188860
  have htrace : WordTrace (prefixWord ++ tailWord_3188860) baseStart_3188860 baseEnd_3188860 := by
    simpa [prefixWord, tailWord_3188860, baseEnd_3188860] using wordTrace_append hprefix tailTrace_3188860
  have hstable : (prefixWord ++ tailWord_3188860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188860).length < 2 ^ (prefixWord ++ tailWord_3188860).sum := by decide
  have hdescent : baseEnd_3188860 < baseStart_3188860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188909 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3188909 : Nat := 118140960795 + 3188909 * 2 ^ 59
def prefixEnd_3188909 : Nat := 4983230072969 + 3 ^ 40 * 3188909 * 2
def baseEnd_3188909 : Nat := 1091628720299046075047987

theorem tailTrace_3188909 : CollatzResearch.WordTrace tailWord_3188909 prefixEnd_3188909 1091628720299046075047987 := by
  unfold tailWord_3188909
  simp only [CollatzResearch.WordTrace]
  refine ⟨116309066404134790142713781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77539377602756526761809187 116309066404134790142713781)
  ·
    refine ⟨10903974975387636575879417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116309066404134790142713781 10903974975387636575879417)
    ·
      refine ⟨8177981231540727431909563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10903974975387636575879417 8177981231540727431909563)
      ·
        refine ⟨12266971847311091147864345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8177981231540727431909563 12266971847311091147864345)
        ·
          refine ⟨9200228885483318360898259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12266971847311091147864345 9200228885483318360898259)
          ·
            refine ⟨13800343328224977541347389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9200228885483318360898259 13800343328224977541347389)
            ·
              refine ⟨5175128748084366578005271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13800343328224977541347389 5175128748084366578005271)
              ·
                refine ⟨7762693122126549867007907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5175128748084366578005271 7762693122126549867007907)
                ·
                  refine ⟨11644039683189824800511861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7762693122126549867007907 11644039683189824800511861)
                  ·
                    refine ⟨1091628720299046075047987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11644039683189824800511861 1091628720299046075047987)
                    ·
                      rfl

theorem cell22_3188909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3188909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188909 prefixEnd_3188909 := by exact prefixLift 3188909
  have htrace : WordTrace (prefixWord ++ tailWord_3188909) baseStart_3188909 baseEnd_3188909 := by
    simpa [prefixWord, tailWord_3188909, baseEnd_3188909] using wordTrace_append hprefix tailTrace_3188909
  have hstable : (prefixWord ++ tailWord_3188909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188909).length < 2 ^ (prefixWord ++ tailWord_3188909).sum := by decide
  have hdescent : baseEnd_3188909 < baseStart_3188909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188920 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 2, 7]
def baseStart_3188920 : Nat := 118140960795 + 3188920 * 2 ^ 59
def prefixEnd_3188920 : Nat := 4983230072969 + 3 ^ 40 * 3188920 * 2
def baseEnd_3188920 : Nat := 1091632485823845713022953

theorem tailTrace_3188920 : CollatzResearch.WordTrace tailWord_3188920 prefixEnd_3188920 1091632485823845713022953 := by
  unfold tailWord_3188920
  simp only [CollatzResearch.WordTrace]
  refine ⟨58154733803547469510682107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77539645071396626014242809 58154733803547469510682107)
  ·
    refine ⟨87232100705321204266023161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58154733803547469510682107 87232100705321204266023161)
    ·
      refine ⟨65424075528990903199517371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87232100705321204266023161 65424075528990903199517371)
      ·
        refine ⟨98136113293486354799276057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65424075528990903199517371 98136113293486354799276057)
        ·
          refine ⟨73602084970114766099457043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98136113293486354799276057 73602084970114766099457043)
          ·
            refine ⟨110403127455172149149185565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73602084970114766099457043 110403127455172149149185565)
            ·
              refine ⟨41401172795689555930944587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110403127455172149149185565 41401172795689555930944587)
              ·
                refine ⟨62101759193534333896416881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41401172795689555930944587 62101759193534333896416881)
                ·
                  refine ⟨46576319395150750422312661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62101759193534333896416881 46576319395150750422312661)
                  ·
                    refine ⟨1091632485823845713022953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46576319395150750422312661 1091632485823845713022953)
                    ·
                      rfl

theorem cell22_3188920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_3188920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188920 prefixEnd_3188920 := by exact prefixLift 3188920
  have htrace : WordTrace (prefixWord ++ tailWord_3188920) baseStart_3188920 baseEnd_3188920 := by
    simpa [prefixWord, tailWord_3188920, baseEnd_3188920] using wordTrace_append hprefix tailTrace_3188920
  have hstable : (prefixWord ++ tailWord_3188920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188920).length < 2 ^ (prefixWord ++ tailWord_3188920).sum := by decide
  have hdescent : baseEnd_3188920 < baseStart_3188920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188922 : List Nat := [3, 1, 1, 1, 2, 2, 6, 6]
def baseStart_3188922 : Nat := 118140960795 + 3188922 * 2 ^ 59
def prefixEnd_3188922 : Nat := 4983230072969 + 3 ^ 40 * 3188922 * 2
def baseEnd_3188922 : Nat := 121292574496079819385883

theorem tailTrace_3188922 : CollatzResearch.WordTrace tailWord_3188922 prefixEnd_3188922 121292574496079819385883 := by
  unfold tailWord_3188922
  simp only [CollatzResearch.WordTrace]
  refine ⟨29077385138271923340734255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77539693702058462241958013 29077385138271923340734255)
  ·
    refine ⟨43616077707407885011101383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29077385138271923340734255 43616077707407885011101383)
    ·
      refine ⟨65424116561111827516652075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43616077707407885011101383 65424116561111827516652075)
      ·
        refine ⟨98136174841667741274978113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65424116561111827516652075 98136174841667741274978113)
        ·
          refine ⟨73602131131250805956233585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98136174841667741274978113 73602131131250805956233585)
          ·
            refine ⟨55201598348438104467175189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73602131131250805956233585 55201598348438104467175189)
            ·
              refine ⟨2587574922583036146898837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55201598348438104467175189 2587574922583036146898837)
              ·
                refine ⟨121292574496079819385883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2587574922583036146898837 121292574496079819385883)
                ·
                  rfl

theorem cell22_3188922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 6].length) (baseStart_3188922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188922 prefixEnd_3188922 := by exact prefixLift 3188922
  have htrace : WordTrace (prefixWord ++ tailWord_3188922) baseStart_3188922 baseEnd_3188922 := by
    simpa [prefixWord, tailWord_3188922, baseEnd_3188922] using wordTrace_append hprefix tailTrace_3188922
  have hstable : (prefixWord ++ tailWord_3188922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188922).length < 2 ^ (prefixWord ++ tailWord_3188922).sum := by decide
  have hdescent : baseEnd_3188922 < baseStart_3188922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188935 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3188935 : Nat := 118140960795 + 3188935 * 2 ^ 59
def prefixEnd_3188935 : Nat := 4983230072969 + 3 ^ 40 * 3188935 * 2
def baseEnd_3188935 : Nat := 1091637620630390673897907

theorem tailTrace_3188935 : CollatzResearch.WordTrace tailWord_3188935 prefixEnd_3188935 1091637620630390673897907 := by
  unfold tailWord_3188935
  simp only [CollatzResearch.WordTrace]
  refine ⟨116310014702040596583160259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77540009801360397722106839 116310014702040596583160259)
  ·
    refine ⟨174465022053060894874740389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116310014702040596583160259 174465022053060894874740389)
    ·
      refine ⟨32712191634948917789013823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174465022053060894874740389 32712191634948917789013823)
      ·
        refine ⟨49068287452423376683520735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32712191634948917789013823 49068287452423376683520735)
        ·
          refine ⟨73602431178635065025281103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49068287452423376683520735 73602431178635065025281103)
          ·
            refine ⟨110403646767952597537921655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73602431178635065025281103 110403646767952597537921655)
            ·
              refine ⟨165605470151928896306882483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110403646767952597537921655 165605470151928896306882483)
              ·
                refine ⟨248408205227893344460323725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165605470151928896306882483 248408205227893344460323725)
                ·
                  refine ⟨93153076960460004172621397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248408205227893344460323725 93153076960460004172621397)
                  ·
                    refine ⟨1091637620630390673897907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93153076960460004172621397 1091637620630390673897907)
                    ·
                      rfl

theorem cell22_3188935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3188935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188935 prefixEnd_3188935 := by exact prefixLift 3188935
  have htrace : WordTrace (prefixWord ++ tailWord_3188935) baseStart_3188935 baseEnd_3188935 := by
    simpa [prefixWord, tailWord_3188935, baseEnd_3188935] using wordTrace_append hprefix tailTrace_3188935
  have hstable : (prefixWord ++ tailWord_3188935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188935).length < 2 ^ (prefixWord ++ tailWord_3188935).sum := by decide
  have hdescent : baseEnd_3188935 < baseStart_3188935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188954 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 3, 3]
def baseStart_3188954 : Nat := 118140960795 + 3188954 * 2 ^ 59
def prefixEnd_3188954 : Nat := 4983230072969 + 3 ^ 40 * 3188954 * 2
def baseEnd_3188954 : Nat := 1091644124718680957672849

theorem tailTrace_3188954 : CollatzResearch.WordTrace tailWord_3188954 prefixEnd_3188954 1091644124718680957672849 := by
  unfold tailWord_3188954
  simp only [CollatzResearch.WordTrace]
  refine ⟨29077676922242940707025479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77540471792647841885401277 29077676922242940707025479)
  ·
    refine ⟨43616515383364411060538219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29077676922242940707025479 43616515383364411060538219)
    ·
      refine ⟨65424773075046616590807329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43616515383364411060538219 65424773075046616590807329)
      ·
        refine ⟨49068579806284962443105497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65424773075046616590807329 49068579806284962443105497)
        ·
          refine ⟨36801434854713721832329123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49068579806284962443105497 36801434854713721832329123)
          ·
            refine ⟨55202152282070582748493685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36801434854713721832329123 55202152282070582748493685)
            ·
              refine ⟨5175201776444117132671283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55202152282070582748493685 5175201776444117132671283)
              ·
                refine ⟨7762802664666175699006925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5175201776444117132671283 7762802664666175699006925)
                ·
                  refine ⟨2911050999249815887127597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7762802664666175699006925 2911050999249815887127597)
                  ·
                    refine ⟨1091644124718680957672849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2911050999249815887127597 1091644124718680957672849)
                    ·
                      rfl

theorem cell22_3188954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_3188954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188954 prefixEnd_3188954 := by exact prefixLift 3188954
  have htrace : WordTrace (prefixWord ++ tailWord_3188954) baseStart_3188954 baseEnd_3188954 := by
    simpa [prefixWord, tailWord_3188954, baseEnd_3188954] using wordTrace_append hprefix tailTrace_3188954
  have hstable : (prefixWord ++ tailWord_3188954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188954).length < 2 ^ (prefixWord ++ tailWord_3188954).sum := by decide
  have hdescent : baseEnd_3188954 < baseStart_3188954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188956 : List Nat := [2, 2, 5, 2, 1, 1, 2, 7]
def baseStart_3188956 : Nat := 118140960795 + 3188956 * 2 ^ 59
def prefixEnd_3188956 : Nat := 4983230072969 + 3 ^ 40 * 3188956 * 2
def baseEnd_3188956 : Nat := 121293867706617068791427

theorem tailTrace_3188956 : CollatzResearch.WordTrace tailWord_3188956 prefixEnd_3188956 121293867706617068791427 := by
  unfold tailWord_3188956
  simp only [CollatzResearch.WordTrace]
  refine ⟨58155390317482258584837361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77540520423309678113116481 58155390317482258584837361)
  ·
    refine ⟨43616542738111693938628021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58155390317482258584837361 43616542738111693938628021)
    ·
      refine ⟨4089050881697971306746377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43616542738111693938628021 4089050881697971306746377)
      ·
        refine ⟨3066788161273478480059783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4089050881697971306746377 3066788161273478480059783)
        ·
          refine ⟨4600182241910217720089675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3066788161273478480059783 4600182241910217720089675)
          ·
            refine ⟨6900273362865326580134513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600182241910217720089675 6900273362865326580134513)
            ·
              refine ⟨5175205022148994935100885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6900273362865326580134513 5175205022148994935100885)
              ·
                refine ⟨121293867706617068791427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5175205022148994935100885 121293867706617068791427)
                ·
                  rfl

theorem cell22_3188956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 7].length) (baseStart_3188956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3188956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3188956 prefixEnd_3188956 := by exact prefixLift 3188956
  have htrace : WordTrace (prefixWord ++ tailWord_3188956) baseStart_3188956 baseEnd_3188956 := by
    simpa [prefixWord, tailWord_3188956, baseEnd_3188956] using wordTrace_append hprefix tailTrace_3188956
  have hstable : (prefixWord ++ tailWord_3188956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188956).length < 2 ^ (prefixWord ++ tailWord_3188956).sum := by decide
  have hdescent : baseEnd_3188956 < baseStart_3188956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189029 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 6]
def baseStart_3189029 : Nat := 118140960795 + 3189029 * 2 ^ 59
def prefixEnd_3189029 : Nat := 4983230072969 + 3 ^ 40 * 3189029 * 2
def baseEnd_3189029 : Nat := 363889932917135254015873

theorem tailTrace_3189029 : CollatzResearch.WordTrace tailWord_3189029 prefixEnd_3189029 363889932917135254015873 := by
  unfold tailWord_3189029
  simp only [CollatzResearch.WordTrace]
  refine ⟨116313443163700050637082141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77542295442466700424721427 116313443163700050637082141)
  ·
    refine ⟨43617541186387518988905803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116313443163700050637082141 43617541186387518988905803)
    ·
      refine ⟨65426311779581278483358705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43617541186387518988905803 65426311779581278483358705)
      ·
        refine ⟨49069733834685958862519029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65426311779581278483358705 49069733834685958862519029)
        ·
          refine ⟨4600287547001808643361159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49069733834685958862519029 4600287547001808643361159)
          ·
            refine ⟨6900431320502712965041739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600287547001808643361159 6900431320502712965041739)
            ·
              refine ⟨10350646980754069447562609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6900431320502712965041739 10350646980754069447562609)
              ·
                refine ⟨7762985235565552085671957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10350646980754069447562609 7762985235565552085671957)
                ·
                  refine ⟨363889932917135254015873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7762985235565552085671957 363889932917135254015873)
                  ·
                    rfl

theorem cell22_3189029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_3189029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189029 prefixEnd_3189029 := by exact prefixLift 3189029
  have htrace : WordTrace (prefixWord ++ tailWord_3189029) baseStart_3189029 baseEnd_3189029 := by
    simpa [prefixWord, tailWord_3189029, baseEnd_3189029] using wordTrace_append hprefix tailTrace_3189029
  have hstable : (prefixWord ++ tailWord_3189029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189029).length < 2 ^ (prefixWord ++ tailWord_3189029).sum := by decide
  have hdescent : baseEnd_3189029 < baseStart_3189029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189087 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 2, 6]
def baseStart_3189087 : Nat := 118140960795 + 3189087 * 2 ^ 59
def prefixEnd_3189087 : Nat := 4983230072969 + 3 ^ 40 * 3189087 * 2
def baseEnd_3189087 : Nat := 1091689653336712944097441

theorem tailTrace_3189087 : CollatzResearch.WordTrace tailWord_3189087 prefixEnd_3189087 1091689653336712944097441 := by
  unfold tailWord_3189087
  simp only [CollatzResearch.WordTrace]
  refine ⟨116315558597489926542693515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77543705731659951028462343 116315558597489926542693515)
  ·
    refine ⟨174473337896234889814040273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116315558597489926542693515 174473337896234889814040273)
    ·
      refine ⟨130855003422176167360530205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174473337896234889814040273 130855003422176167360530205)
      ·
        refine ⟨49070626283316062760198827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130855003422176167360530205 49070626283316062760198827)
        ·
          refine ⟨73605939424974094140298241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49070626283316062760198827 73605939424974094140298241)
          ·
            refine ⟨55204454568730570605223681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73605939424974094140298241 55204454568730570605223681)
            ·
              refine ⟨41403340926547927953917761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55204454568730570605223681 41403340926547927953917761)
              ·
                refine ⟨31052505694910945965438321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41403340926547927953917761 31052505694910945965438321)
                ·
                  refine ⟨23289379271183209474078741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31052505694910945965438321 23289379271183209474078741)
                  ·
                    refine ⟨1091689653336712944097441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23289379271183209474078741 1091689653336712944097441)
                    ·
                      rfl

theorem cell22_3189087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_3189087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189087 prefixEnd_3189087 := by exact prefixLift 3189087
  have htrace : WordTrace (prefixWord ++ tailWord_3189087) baseStart_3189087 baseEnd_3189087 := by
    simpa [prefixWord, tailWord_3189087, baseEnd_3189087] using wordTrace_append hprefix tailTrace_3189087
  have hstable : (prefixWord ++ tailWord_3189087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189087).length < 2 ^ (prefixWord ++ tailWord_3189087).sum := by decide
  have hdescent : baseEnd_3189087 < baseStart_3189087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189123 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 3, 3]
def baseStart_3189123 : Nat := 118140960795 + 3189123 * 2 ^ 59
def prefixEnd_3189123 : Nat := 4983230072969 + 3 ^ 40 * 3189123 * 2
def baseEnd_3189123 : Nat := 1091701976872420850197331

theorem tailTrace_3189123 : CollatzResearch.WordTrace tailWord_3189123 prefixEnd_3189123 1091701976872420850197331 := by
  unfold tailWord_3189123
  simp only [CollatzResearch.WordTrace]
  refine ⟨116316871625359504691004023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77544581083573003127336015 116316871625359504691004023)
  ·
    refine ⟨174475307438039257036506035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116316871625359504691004023 174475307438039257036506035)
    ·
      refine ⟨261712961157058885554759053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174475307438039257036506035 261712961157058885554759053)
      ·
        refine ⟨98142360433897082083034645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261712961157058885554759053 98142360433897082083034645)
        ·
          refine ⟨4600423145338925722642249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98142360433897082083034645 4600423145338925722642249)
          ·
            refine ⟨3450317359004194291981687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4600423145338925722642249 3450317359004194291981687)
            ·
              refine ⟨5175476038506291437972531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450317359004194291981687 5175476038506291437972531)
              ·
                refine ⟨7763214057759437156958797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5175476038506291437972531 7763214057759437156958797)
                ·
                  refine ⟨2911205271659788933859549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7763214057759437156958797 2911205271659788933859549)
                  ·
                    refine ⟨1091701976872420850197331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2911205271659788933859549 1091701976872420850197331)
                    ·
                      rfl

theorem cell22_3189123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 3].length) (baseStart_3189123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189123 prefixEnd_3189123 := by exact prefixLift 3189123
  have htrace : WordTrace (prefixWord ++ tailWord_3189123) baseStart_3189123 baseEnd_3189123 := by
    simpa [prefixWord, tailWord_3189123, baseEnd_3189123] using wordTrace_append hprefix tailTrace_3189123
  have hstable : (prefixWord ++ tailWord_3189123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189123).length < 2 ^ (prefixWord ++ tailWord_3189123).sum := by decide
  have hdescent : baseEnd_3189123 < baseStart_3189123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189185 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3189185 : Nat := 118140960795 + 3189185 * 2 ^ 59
def prefixEnd_3189185 : Nat := 4983230072969 + 3 ^ 40 * 3189185 * 2
def baseEnd_3189185 : Nat := 1091723200739473355147141

theorem tailTrace_3189185 : CollatzResearch.WordTrace tailWord_3189185 prefixEnd_3189185 1091723200739473355147141 := by
  unfold tailWord_3189185
  simp only [CollatzResearch.WordTrace]
  refine ⟨116319132951134889279761009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77546088634089926186507339 116319132951134889279761009)
  ·
    refine ⟨87239349713351166959820757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116319132951134889279761009 87239349713351166959820757)
    ·
      refine ⟨2044672258906667975620799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 87239349713351166959820757 2044672258906667975620799)
      ·
        refine ⟨3067008388360001963431199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044672258906667975620799 3067008388360001963431199)
        ·
          refine ⟨4600512582540002945146799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3067008388360001963431199 4600512582540002945146799)
          ·
            refine ⟨6900768873810004417720199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600512582540002945146799 6900768873810004417720199)
            ·
              refine ⟨10351153310715006626580299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6900768873810004417720199 10351153310715006626580299)
              ·
                refine ⟨15526729966072509939870449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10351153310715006626580299 15526729966072509939870449)
                ·
                  refine ⟨11645047474554382454902837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15526729966072509939870449 11645047474554382454902837)
                  ·
                    refine ⟨1091723200739473355147141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11645047474554382454902837 1091723200739473355147141)
                    ·
                      rfl

theorem cell22_3189185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3189185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189185 prefixEnd_3189185 := by exact prefixLift 3189185
  have htrace : WordTrace (prefixWord ++ tailWord_3189185) baseStart_3189185 baseEnd_3189185 := by
    simpa [prefixWord, tailWord_3189185, baseEnd_3189185] using wordTrace_append hprefix tailTrace_3189185
  have hstable : (prefixWord ++ tailWord_3189185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189185).length < 2 ^ (prefixWord ++ tailWord_3189185).sum := by decide
  have hdescent : baseEnd_3189185 < baseStart_3189185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189194 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_3189194 : Nat := 118140960795 + 3189194 * 2 ^ 59
def prefixEnd_3189194 : Nat := 4983230072969 + 3 ^ 40 * 3189194 * 2
def baseEnd_3189194 : Nat := 1091726281623400331672113

theorem tailTrace_3189194 : CollatzResearch.WordTrace tailWord_3189194 prefixEnd_3189194 1091726281623400331672113 := by
  unfold tailWord_3189194
  simp only [CollatzResearch.WordTrace]
  refine ⟨29079865302025570954209659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77546307472068189211225757 29079865302025570954209659)
  ·
    refine ⟨43619797953038356431314489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29079865302025570954209659 43619797953038356431314489)
    ·
      refine ⟨32714848464778767323485867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43619797953038356431314489 32714848464778767323485867)
      ·
        refine ⟨49072272697168150985228801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32714848464778767323485867 49072272697168150985228801)
        ·
          refine ⟨36804204522876113238921601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49072272697168150985228801 36804204522876113238921601)
          ·
            refine ⟨27603153392157084929191201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36804204522876113238921601 27603153392157084929191201)
            ·
              refine ⟨20702365044117813696893401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27603153392157084929191201 20702365044117813696893401)
              ·
                refine ⟨15526773783088360272670051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20702365044117813696893401 15526773783088360272670051)
                ·
                  refine ⟨23290160674632540409005077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15526773783088360272670051 23290160674632540409005077)
                  ·
                    refine ⟨1091726281623400331672113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23290160674632540409005077 1091726281623400331672113)
                    ·
                      rfl

theorem cell22_3189194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_3189194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189194 prefixEnd_3189194 := by exact prefixLift 3189194
  have htrace : WordTrace (prefixWord ++ tailWord_3189194) baseStart_3189194 baseEnd_3189194 := by
    simpa [prefixWord, tailWord_3189194, baseEnd_3189194] using wordTrace_append hprefix tailTrace_3189194
  have hstable : (prefixWord ++ tailWord_3189194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189194).length < 2 ^ (prefixWord ++ tailWord_3189194).sum := by decide
  have hdescent : baseEnd_3189194 < baseStart_3189194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189230 : List Nat := [4, 1, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_3189230 : Nat := 118140960795 + 3189230 * 2 ^ 59
def prefixEnd_3189230 : Nat := 4983230072969 + 3 ^ 40 * 3189230 * 2
def baseEnd_3189230 : Nat := 1091738605159108237772003

theorem tailTrace_3189230 : CollatzResearch.WordTrace tailWord_3189230 prefixEnd_3189230 1091738605159108237772003 := by
  unfold tailWord_3189230
  simp only [CollatzResearch.WordTrace]
  refine ⟨14540096779496482745643643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77547182823981241310099429 14540096779496482745643643)
  ·
    refine ⟨21810145169244724118465465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14540096779496482745643643 21810145169244724118465465)
    ·
      refine ⟨16357608876933543088849099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21810145169244724118465465 16357608876933543088849099)
      ·
        refine ⟨24536413315400314633273649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16357608876933543088849099 24536413315400314633273649)
        ·
          refine ⟨18402309986550235974955237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24536413315400314633273649 18402309986550235974955237)
          ·
            refine ⟨3450433122478169245304107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18402309986550235974955237 3450433122478169245304107)
            ·
              refine ⟨5175649683717253867956161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450433122478169245304107 5175649683717253867956161)
              ·
                refine ⟨3881737262787940400967121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5175649683717253867956161 3881737262787940400967121)
                ·
                  refine ⟨2911302947090955300725341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3881737262787940400967121 2911302947090955300725341)
                  ·
                    refine ⟨1091738605159108237772003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2911302947090955300725341 1091738605159108237772003)
                    ·
                      rfl

theorem cell22_3189230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_3189230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189230 prefixEnd_3189230 := by exact prefixLift 3189230
  have htrace : WordTrace (prefixWord ++ tailWord_3189230) baseStart_3189230 baseEnd_3189230 := by
    simpa [prefixWord, tailWord_3189230, baseEnd_3189230] using wordTrace_append hprefix tailTrace_3189230
  have hstable : (prefixWord ++ tailWord_3189230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189230).length < 2 ^ (prefixWord ++ tailWord_3189230).sum := by decide
  have hdescent : baseEnd_3189230 < baseStart_3189230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189241 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 3, 3]
def baseStart_3189241 : Nat := 118140960795 + 3189241 * 2 ^ 59
def prefixEnd_3189241 : Nat := 4983230072969 + 3 ^ 40 * 3189241 * 2
def baseEnd_3189241 : Nat := 1091742370683907875746969

theorem tailTrace_3189241 : CollatzResearch.WordTrace tailWord_3189241 prefixEnd_3189241 1091742370683907875746969 := by
  unfold tailWord_3189241
  simp only [CollatzResearch.WordTrace]
  refine ⟨116321175438932010843799577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77547450292621340562533051 116321175438932010843799577)
  ·
    refine ⟨87240881579199008132849683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116321175438932010843799577 87240881579199008132849683)
    ·
      refine ⟨130861322368798512199274525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87240881579199008132849683 130861322368798512199274525)
      ·
        refine ⟨49072995888299442074727947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130861322368798512199274525 49072995888299442074727947)
        ·
          refine ⟨73609493832449163112091921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49072995888299442074727947 73609493832449163112091921)
          ·
            refine ⟨55207120374336872334068941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73609493832449163112091921 55207120374336872334068941)
            ·
              refine ⟨20702670140376327125275853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55207120374336872334068941 20702670140376327125275853)
              ·
                refine ⟨7763501302641122671978445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20702670140376327125275853 7763501302641122671978445)
                ·
                  refine ⟨2911312988490421001991917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7763501302641122671978445 2911312988490421001991917)
                  ·
                    refine ⟨1091742370683907875746969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2911312988490421001991917 1091742370683907875746969)
                    ·
                      rfl

theorem cell22_3189241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 3].length) (baseStart_3189241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189241 prefixEnd_3189241 := by exact prefixLift 3189241
  have htrace : WordTrace (prefixWord ++ tailWord_3189241) baseStart_3189241 baseEnd_3189241 := by
    simpa [prefixWord, tailWord_3189241, baseEnd_3189241] using wordTrace_append hprefix tailTrace_3189241
  have hstable : (prefixWord ++ tailWord_3189241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189241).length < 2 ^ (prefixWord ++ tailWord_3189241).sum := by decide
  have hdescent : baseEnd_3189241 < baseStart_3189241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189301 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3189301 : Nat := 118140960795 + 3189301 * 2 ^ 59
def prefixEnd_3189301 : Nat := 4983230072969 + 3 ^ 40 * 3189301 * 2
def baseEnd_3189301 : Nat := 1091762909910087719246785

theorem tailTrace_3189301 : CollatzResearch.WordTrace tailWord_3189301 prefixEnd_3189301 1091762909910087719246785 := by
  unfold tailWord_3189301
  simp only [CollatzResearch.WordTrace]
  refine ⟨116323363818714641090983757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77548909212476427393989171 116323363818714641090983757)
  ·
    refine ⟨43621261432017990409118909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116323363818714641090983757 43621261432017990409118909)
    ·
      refine ⟨16357973037006746403419591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43621261432017990409118909 16357973037006746403419591)
      ·
        refine ⟨24536959555510119605129387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16357973037006746403419591 24536959555510119605129387)
        ·
          refine ⟨36805439333265179407694081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24536959555510119605129387 36805439333265179407694081)
          ·
            refine ⟨27604079499948884555770561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36805439333265179407694081 27604079499948884555770561)
            ·
              refine ⟨20703059624961663416827921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27604079499948884555770561 20703059624961663416827921)
              ·
                refine ⟨15527294718721247562620941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20703059624961663416827921 15527294718721247562620941)
                ·
                  refine ⟨5822735519520467835982853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15527294718721247562620941 5822735519520467835982853)
                  ·
                    refine ⟨1091762909910087719246785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5822735519520467835982853 1091762909910087719246785)
                    ·
                      rfl

theorem cell22_3189301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3189301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189301 prefixEnd_3189301 := by exact prefixLift 3189301
  have htrace : WordTrace (prefixWord ++ tailWord_3189301) baseStart_3189301 baseEnd_3189301 := by
    simpa [prefixWord, tailWord_3189301, baseEnd_3189301] using wordTrace_append hprefix tailTrace_3189301
  have hstable : (prefixWord ++ tailWord_3189301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189301).length < 2 ^ (prefixWord ++ tailWord_3189301).sum := by decide
  have hdescent : baseEnd_3189301 < baseStart_3189301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189365 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 1, 5]
def baseStart_3189365 : Nat := 118140960795 + 3189365 * 2 ^ 59
def prefixEnd_3189365 : Nat := 4983230072969 + 3 ^ 40 * 3189365 * 2
def baseEnd_3189365 : Nat := 1091784818418012885646589

theorem tailTrace_3189365 : CollatzResearch.WordTrace tailWord_3189365 prefixEnd_3189365 1091784818418012885646589 := by
  unfold tailWord_3189365
  simp only [CollatzResearch.WordTrace]
  refine ⟨116325698090482780021313549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77550465393655186680875699 116325698090482780021313549)
  ·
    refine ⟨43622136783931042507992581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116325698090482780021313549 43622136783931042507992581)
    ·
      refine ⟨8179150646987070470248609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43622136783931042507992581 8179150646987070470248609)
      ·
        refine ⟨6134362985240302852686457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8179150646987070470248609 6134362985240302852686457)
        ·
          refine ⟨4600772238930227139514843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6134362985240302852686457 4600772238930227139514843)
          ·
            refine ⟨6901158358395340709272265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600772238930227139514843 6901158358395340709272265)
            ·
              refine ⟨5175868768796505531954199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6901158358395340709272265 5175868768796505531954199)
              ·
                refine ⟨7763803153194758297931299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5175868768796505531954199 7763803153194758297931299)
                ·
                  refine ⟨11645704729792137446896949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7763803153194758297931299 11645704729792137446896949)
                  ·
                    refine ⟨1091784818418012885646589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11645704729792137446896949 1091784818418012885646589)
                    ·
                      rfl

theorem cell22_3189365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_3189365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189365 prefixEnd_3189365 := by exact prefixLift 3189365
  have htrace : WordTrace (prefixWord ++ tailWord_3189365) baseStart_3189365 baseEnd_3189365 := by
    simpa [prefixWord, tailWord_3189365, baseEnd_3189365] using wordTrace_append hprefix tailTrace_3189365
  have hstable : (prefixWord ++ tailWord_3189365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189365).length < 2 ^ (prefixWord ++ tailWord_3189365).sum := by decide
  have hdescent : baseEnd_3189365 < baseStart_3189365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189380 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_3189380 : Nat := 118140960795 + 3189380 * 2 ^ 59
def prefixEnd_3189380 : Nat := 4983230072969 + 3 ^ 40 * 3189380 * 2
def baseEnd_3189380 : Nat := 1091789953224557846521543

theorem tailTrace_3189380 : CollatzResearch.WordTrace tailWord_3189380 prefixEnd_3189380 1091789953224557846521543 := by
  unfold tailWord_3189380
  simp only [CollatzResearch.WordTrace]
  refine ⟨58163122592714218791554797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77550830123618958388739729 58163122592714218791554797)
  ·
    refine ⟨21811170972267832046833049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58163122592714218791554797 21811170972267832046833049)
    ·
      refine ⟨16358378229200874035124787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21811170972267832046833049 16358378229200874035124787)
      ·
        refine ⟨24537567343801311052687181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16358378229200874035124787 24537567343801311052687181)
        ·
          refine ⟨9201587753925491644757693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24537567343801311052687181 9201587753925491644757693)
          ·
            refine ⟨3450595407722059366784135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9201587753925491644757693 3450595407722059366784135)
            ·
              refine ⟨5175893111583089050176203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450595407722059366784135 5175893111583089050176203)
              ·
                refine ⟨7763839667374633575264305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5175893111583089050176203 7763839667374633575264305)
                ·
                  refine ⟨5822879750530975181448229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7763839667374633575264305 5822879750530975181448229)
                  ·
                    refine ⟨1091789953224557846521543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5822879750530975181448229 1091789953224557846521543)
                    ·
                      rfl

theorem cell22_3189380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_3189380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189380 prefixEnd_3189380 := by exact prefixLift 3189380
  have htrace : WordTrace (prefixWord ++ tailWord_3189380) baseStart_3189380 baseEnd_3189380 := by
    simpa [prefixWord, tailWord_3189380, baseEnd_3189380] using wordTrace_append hprefix tailTrace_3189380
  have hstable : (prefixWord ++ tailWord_3189380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189380).length < 2 ^ (prefixWord ++ tailWord_3189380).sum := by decide
  have hdescent : baseEnd_3189380 < baseStart_3189380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189444 : List Nat := [2, 3, 3, 1, 1, 4, 1, 3, 1, 3]
def baseStart_3189444 : Nat := 118140960795 + 3189444 * 2 ^ 59
def prefixEnd_3189444 : Nat := 4983230072969 + 3 ^ 40 * 3189444 * 2
def baseEnd_3189444 : Nat := 1091811861732483012921347

theorem tailTrace_3189444 : CollatzResearch.WordTrace tailWord_3189444 prefixEnd_3189444 1091811861732483012921347 := by
  unfold tailWord_3189444
  simp only [CollatzResearch.WordTrace]
  refine ⟨58164289728598288256719693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77552386304797717675626257 58164289728598288256719693)
  ·
    refine ⟨21811608648224358096269885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58164289728598288256719693 21811608648224358096269885)
    ·
      refine ⟨8179353243084134286101207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21811608648224358096269885 8179353243084134286101207)
      ·
        refine ⟨12269029864626201429151811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8179353243084134286101207 12269029864626201429151811)
        ·
          refine ⟨18403544796939302143727717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12269029864626201429151811 18403544796939302143727717)
          ·
            refine ⟨3450664649426119151948947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18403544796939302143727717 3450664649426119151948947)
            ·
              refine ⟨5175996974139178727923421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450664649426119151948947 5175996974139178727923421)
              ·
                refine ⟨1940998865302192022971283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5175996974139178727923421 1940998865302192022971283)
                ·
                  refine ⟨2911498297953288034456925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1940998865302192022971283 2911498297953288034456925)
                  ·
                    refine ⟨1091811861732483012921347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2911498297953288034456925 1091811861732483012921347)
                    ·
                      rfl

theorem cell22_3189444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_3189444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189444 prefixEnd_3189444 := by exact prefixLift 3189444
  have htrace : WordTrace (prefixWord ++ tailWord_3189444) baseStart_3189444 baseEnd_3189444 := by
    simpa [prefixWord, tailWord_3189444, baseEnd_3189444] using wordTrace_append hprefix tailTrace_3189444
  have hstable : (prefixWord ++ tailWord_3189444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189444).length < 2 ^ (prefixWord ++ tailWord_3189444).sum := by decide
  have hdescent : baseEnd_3189444 < baseStart_3189444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189461 : List Nat := [1, 3, 2, 5, 1, 1, 3, 2, 1, 3]
def baseStart_3189461 : Nat := 118140960795 + 3189461 * 2 ^ 59
def prefixEnd_3189461 : Nat := 4983230072969 + 3 ^ 40 * 3189461 * 2
def baseEnd_3189461 : Nat := 1091817681179900635246295

theorem tailTrace_3189461 : CollatzResearch.WordTrace tailWord_3189461 prefixEnd_3189461 1091817681179900635246295 := by
  unfold tailWord_3189461
  simp only [CollatzResearch.WordTrace]
  refine ⟨116329199498134988416808237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77552799665423325611205491 116329199498134988416808237)
  ·
    refine ⟨43623449811800620656303089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116329199498134988416808237 43623449811800620656303089)
    ·
      refine ⟨32717587358850465492227317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43623449811800620656303089 32717587358850465492227317)
      ·
        refine ⟨3067273814892231139896311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32717587358850465492227317 3067273814892231139896311)
        ·
          refine ⟨4600910722338346709844467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3067273814892231139896311 4600910722338346709844467)
          ·
            refine ⟨6901366083507520064766701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600910722338346709844467 6901366083507520064766701)
            ·
              refine ⟨2588012281315320024287513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6901366083507520064766701 2588012281315320024287513)
              ·
                refine ⟨1941009210986490018215635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2588012281315320024287513 1941009210986490018215635)
                ·
                  refine ⟨2911513816479735027323453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941009210986490018215635 2911513816479735027323453)
                  ·
                    refine ⟨1091817681179900635246295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2911513816479735027323453 1091817681179900635246295)
                    ·
                      rfl

theorem cell22_3189461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_3189461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189461 prefixEnd_3189461 := by exact prefixLift 3189461
  have htrace : WordTrace (prefixWord ++ tailWord_3189461) baseStart_3189461 baseEnd_3189461 := by
    simpa [prefixWord, tailWord_3189461, baseEnd_3189461] using wordTrace_append hprefix tailTrace_3189461
  have hstable : (prefixWord ++ tailWord_3189461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189461).length < 2 ^ (prefixWord ++ tailWord_3189461).sum := by decide
  have hdescent : baseEnd_3189461 < baseStart_3189461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189481 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 3, 6]
def baseStart_3189481 : Nat := 118140960795 + 3189481 * 2 ^ 59
def prefixEnd_3189481 : Nat := 4983230072969 + 3 ^ 40 * 3189481 * 2
def baseEnd_3189481 : Nat := 1091824527588627249746233

theorem tailTrace_3189481 : CollatzResearch.WordTrace tailWord_3189481 prefixEnd_3189481 1091824527588627249746233 := by
  unfold tailWord_3189481
  simp only [CollatzResearch.WordTrace]
  refine ⟨116329928958062531832536297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77553285972041687888357531 116329928958062531832536297)
  ·
    refine ⟨87247446718546898874402223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116329928958062531832536297 87247446718546898874402223)
    ·
      refine ⟨130871170077820348311603335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87247446718546898874402223 130871170077820348311603335)
      ·
        refine ⟨196306755116730522467405003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130871170077820348311603335 196306755116730522467405003)
        ·
          refine ⟨294460132675095783701107505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196306755116730522467405003 294460132675095783701107505)
          ·
            refine ⟨220845099506321837775830629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294460132675095783701107505 220845099506321837775830629)
            ·
              refine ⟨41408456157435344582968243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220845099506321837775830629 41408456157435344582968243)
              ·
                refine ⟨62112684236153016874452365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41408456157435344582968243 62112684236153016874452365)
                ·
                  refine ⟨23292256588557381327919637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62112684236153016874452365 23292256588557381327919637)
                  ·
                    refine ⟨1091824527588627249746233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23292256588557381327919637 1091824527588627249746233)
                    ·
                      rfl

theorem cell22_3189481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_3189481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189481 prefixEnd_3189481 := by exact prefixLift 3189481
  have htrace : WordTrace (prefixWord ++ tailWord_3189481) baseStart_3189481 baseEnd_3189481 := by
    simpa [prefixWord, tailWord_3189481, baseEnd_3189481] using wordTrace_append hprefix tailTrace_3189481
  have hstable : (prefixWord ++ tailWord_3189481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189481).length < 2 ^ (prefixWord ++ tailWord_3189481).sum := by decide
  have hdescent : baseEnd_3189481 < baseStart_3189481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189496 : List Nat := [2, 1, 2, 1, 1, 2, 3, 10]
def baseStart_3189496 : Nat := 118140960795 + 3189496 * 2 ^ 59
def prefixEnd_3189496 : Nat := 4983230072969 + 3 ^ 40 * 3189496 * 2
def baseEnd_3189496 : Nat := 121314406932796912291243

theorem tailTrace_3189496 : CollatzResearch.WordTrace tailWord_3189496 prefixEnd_3189496 121314406932796912291243 := by
  unfold tailWord_3189496
  simp only [CollatzResearch.WordTrace]
  refine ⟨58165238026504094697166171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77553650702005459596221561 58165238026504094697166171)
  ·
    refine ⟨87247857039756142045749257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58165238026504094697166171 87247857039756142045749257)
    ·
      refine ⟨65435892779817106534311943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87247857039756142045749257 65435892779817106534311943)
      ·
        refine ⟨98153839169725659801467915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65435892779817106534311943 98153839169725659801467915)
        ·
          refine ⟨147230758754588489702201873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98153839169725659801467915 147230758754588489702201873)
          ·
            refine ⟨110423069065941367276651405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147230758754588489702201873 110423069065941367276651405)
            ·
              refine ⟨41408650899728012728744277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110423069065941367276651405 41408650899728012728744277)
              ·
                refine ⟨121314406932796912291243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41408650899728012728744277 121314406932796912291243)
                ·
                  rfl

theorem cell22_3189496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 10].length) (baseStart_3189496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189496 prefixEnd_3189496 := by exact prefixLift 3189496
  have htrace : WordTrace (prefixWord ++ tailWord_3189496) baseStart_3189496 baseEnd_3189496 := by
    simpa [prefixWord, tailWord_3189496, baseEnd_3189496] using wordTrace_append hprefix tailTrace_3189496
  have hstable : (prefixWord ++ tailWord_3189496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189496).length < 2 ^ (prefixWord ++ tailWord_3189496).sum := by decide
  have hdescent : baseEnd_3189496 < baseStart_3189496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189498 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_3189498 : Nat := 118140960795 + 3189498 * 2 ^ 59
def prefixEnd_3189498 : Nat := 4983230072969 + 3 ^ 40 * 3189498 * 2
def baseEnd_3189498 : Nat := 1091830347036044872071181

theorem tailTrace_3189498 : CollatzResearch.WordTrace tailWord_3189498 prefixEnd_3189498 1091830347036044872071181 := by
  unfold tailWord_3189498
  simp only [CollatzResearch.WordTrace]
  refine ⟨29082637249750235933976287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77553699332667295823936765 29082637249750235933976287)
  ·
    refine ⟨43623955874625353900964431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29082637249750235933976287 43623955874625353900964431)
    ·
      refine ⟨65435933811938030851446647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43623955874625353900964431 65435933811938030851446647)
      ·
        refine ⟨98153900717907046277169971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65435933811938030851446647 98153900717907046277169971)
        ·
          refine ⟨147230851076860569415754957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98153900717907046277169971 147230851076860569415754957)
          ·
            refine ⟨55211569153822713530908109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147230851076860569415754957 55211569153822713530908109)
            ·
              refine ⟨20704338432683517574090541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55211569153822713530908109 20704338432683517574090541)
              ·
                refine ⟨7764126912256319090283953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20704338432683517574090541 7764126912256319090283953)
                ·
                  refine ⟨5823095184192239317712965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7764126912256319090283953 5823095184192239317712965)
                  ·
                    refine ⟨1091830347036044872071181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5823095184192239317712965 1091830347036044872071181)
                    ·
                      rfl

theorem cell22_3189498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_3189498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189498 prefixEnd_3189498 := by exact prefixLift 3189498
  have htrace : WordTrace (prefixWord ++ tailWord_3189498) baseStart_3189498 baseEnd_3189498 := by
    simpa [prefixWord, tailWord_3189498, baseEnd_3189498] using wordTrace_append hprefix tailTrace_3189498
  have hstable : (prefixWord ++ tailWord_3189498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189498).length < 2 ^ (prefixWord ++ tailWord_3189498).sum := by decide
  have hdescent : baseEnd_3189498 < baseStart_3189498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189605 : List Nat := [1, 3, 1, 3, 1, 1, 3, 4, 1, 4]
def baseStart_3189605 : Nat := 118140960795 + 3189605 * 2 ^ 59
def prefixEnd_3189605 : Nat := 4983230072969 + 3 ^ 40 * 3189605 * 2
def baseEnd_3189605 : Nat := 1091866975322732259645853

theorem tailTrace_3189605 : CollatzResearch.WordTrace tailWord_3189605 prefixEnd_3189605 1091866975322732259645853 := by
  unfold tailWord_3189605
  simp only [CollatzResearch.WordTrace]
  refine ⟨116334451609613301010050269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77556301073075534006700179 116334451609613301010050269)
  ·
    refine ⟨43625419353604987878768851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116334451609613301010050269 43625419353604987878768851)
    ·
      refine ⟨65438129030407481818153277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43625419353604987878768851 65438129030407481818153277)
      ·
        refine ⟨24539298386402805681807479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65438129030407481818153277 24539298386402805681807479)
        ·
          refine ⟨36808947579604208522711219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24539298386402805681807479 36808947579604208522711219)
          ·
            refine ⟨55213421369406312784066829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36808947579604208522711219 55213421369406312784066829)
            ·
              refine ⟨20705033013527367294025061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55213421369406312784066829 20705033013527367294025061)
              ·
                refine ⟨3882193690036381367629699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20705033013527367294025061 3882193690036381367629699)
                ·
                  refine ⟨5823290535054572051444549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3882193690036381367629699 5823290535054572051444549)
                  ·
                    refine ⟨1091866975322732259645853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5823290535054572051444549 1091866975322732259645853)
                    ·
                      rfl

theorem cell22_3189605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_3189605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189605 prefixEnd_3189605 := by exact prefixLift 3189605
  have htrace : WordTrace (prefixWord ++ tailWord_3189605) baseStart_3189605 baseEnd_3189605 := by
    simpa [prefixWord, tailWord_3189605, baseEnd_3189605] using wordTrace_append hprefix tailTrace_3189605
  have hstable : (prefixWord ++ tailWord_3189605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189605).length < 2 ^ (prefixWord ++ tailWord_3189605).sum := by decide
  have hdescent : baseEnd_3189605 < baseStart_3189605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189635 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 4, 3]
def baseStart_3189635 : Nat := 118140960795 + 3189635 * 2 ^ 59
def prefixEnd_3189635 : Nat := 4983230072969 + 3 ^ 40 * 3189635 * 2
def baseEnd_3189635 : Nat := 1091877244935822181395761

theorem tailTrace_3189635 : CollatzResearch.WordTrace tailWord_3189635 prefixEnd_3189635 1091877244935822181395761 := by
  unfold tailWord_3189635
  simp only [CollatzResearch.WordTrace]
  refine ⟨116335545799504616133642359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77557030533003077422428239 116335545799504616133642359)
  ·
    refine ⟨174503318699256924200463539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116335545799504616133642359 174503318699256924200463539)
    ·
      refine ⟨261754978048885386300695309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174503318699256924200463539 261754978048885386300695309)
      ·
        refine ⟨98158116768332019862760741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261754978048885386300695309 98158116768332019862760741)
        ·
          refine ⟨18404646894062253724267639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98158116768332019862760741 18404646894062253724267639)
          ·
            refine ⟨27606970341093380586401459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18404646894062253724267639 27606970341093380586401459)
            ·
              refine ⟨41410455511640070879602189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27606970341093380586401459 41410455511640070879602189)
              ·
                refine ⟨15528920816865026579850821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41410455511640070879602189 15528920816865026579850821)
                ·
                  refine ⟨2911672653162192483722029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15528920816865026579850821 2911672653162192483722029)
                  ·
                    refine ⟨1091877244935822181395761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2911672653162192483722029 1091877244935822181395761)
                    ·
                      rfl

theorem cell22_3189635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 3].length) (baseStart_3189635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189635 prefixEnd_3189635 := by exact prefixLift 3189635
  have htrace : WordTrace (prefixWord ++ tailWord_3189635) baseStart_3189635 baseEnd_3189635 := by
    simpa [prefixWord, tailWord_3189635, baseEnd_3189635] using wordTrace_append hprefix tailTrace_3189635
  have hstable : (prefixWord ++ tailWord_3189635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189635).length < 2 ^ (prefixWord ++ tailWord_3189635).sum := by decide
  have hdescent : baseEnd_3189635 < baseStart_3189635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189665 : List Nat := [1, 2, 3, 4, 1, 1, 2, 8]
def baseStart_3189665 : Nat := 118140960795 + 3189665 * 2 ^ 59
def prefixEnd_3189665 : Nat := 4983230072969 + 3 ^ 40 * 3189665 * 2
def baseEnd_3189665 : Nat := 121320834949879122571741

theorem tailTrace_3189665 : CollatzResearch.WordTrace tailWord_3189665 prefixEnd_3189665 121320834949879122571741 := by
  unfold tailWord_3189665
  simp only [CollatzResearch.WordTrace]
  refine ⟨116336639989395931257234449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77557759992930620838156299 116336639989395931257234449)
  ·
    refine ⟨87252479992046948442925837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116336639989395931257234449 87252479992046948442925837)
    ·
      refine ⟨32719679997017605666097189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87252479992046948442925837 32719679997017605666097189)
      ·
        refine ⟨6134939999440801062393223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32719679997017605666097189 6134939999440801062393223)
        ·
          refine ⟨9202409999161201593589835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6134939999440801062393223 9202409999161201593589835)
          ·
            refine ⟨13803614998741802390384753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9202409999161201593589835 13803614998741802390384753)
            ·
              refine ⟨10352711249056351792788565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13803614998741802390384753 10352711249056351792788565)
              ·
                refine ⟨121320834949879122571741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10352711249056351792788565 121320834949879122571741)
                ·
                  rfl

theorem cell22_3189665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 8].length) (baseStart_3189665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189665 prefixEnd_3189665 := by exact prefixLift 3189665
  have htrace : WordTrace (prefixWord ++ tailWord_3189665) baseStart_3189665 baseEnd_3189665 := by
    simpa [prefixWord, tailWord_3189665, baseEnd_3189665] using wordTrace_append hprefix tailTrace_3189665
  have hstable : (prefixWord ++ tailWord_3189665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189665).length < 2 ^ (prefixWord ++ tailWord_3189665).sum := by decide
  have hdescent : baseEnd_3189665 < baseStart_3189665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189684 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3189684 : Nat := 118140960795 + 3189684 * 2 ^ 59
def prefixEnd_3189684 : Nat := 4983230072969 + 3 ^ 40 * 3189684 * 2
def baseEnd_3189684 : Nat := 1091894018637202386920611

theorem tailTrace_3189684 : CollatzResearch.WordTrace tailWord_3189684 prefixEnd_3189684 1091894018637202386920611 := by
  unfold tailWord_3189684
  simp only [CollatzResearch.WordTrace]
  refine ⟨58168666488163548751088053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77558221984218065001450737 58168666488163548751088053)
  ·
    refine ⟨5453312483265332695414505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58168666488163548751088053 5453312483265332695414505)
    ·
      refine ⟨4089984362448999521560879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5453312483265332695414505 4089984362448999521560879)
      ·
        refine ⟨6134976543673499282341319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4089984362448999521560879 6134976543673499282341319)
        ·
          refine ⟨9202464815510248923511979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6134976543673499282341319 9202464815510248923511979)
          ·
            refine ⟨13803697223265373385267969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9202464815510248923511979 13803697223265373385267969)
            ·
              refine ⟨10352772917449030038950977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13803697223265373385267969 10352772917449030038950977)
              ·
                refine ⟨7764579688086772529213233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10352772917449030038950977 7764579688086772529213233)
                ·
                  refine ⟨5823434766065079396909925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7764579688086772529213233 5823434766065079396909925)
                  ·
                    refine ⟨1091894018637202386920611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5823434766065079396909925 1091894018637202386920611)
                    ·
                      rfl

theorem cell22_3189684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3189684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189684 prefixEnd_3189684 := by exact prefixLift 3189684
  have htrace : WordTrace (prefixWord ++ tailWord_3189684) baseStart_3189684 baseEnd_3189684 := by
    simpa [prefixWord, tailWord_3189684, baseEnd_3189684] using wordTrace_append hprefix tailTrace_3189684
  have hstable : (prefixWord ++ tailWord_3189684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189684).length < 2 ^ (prefixWord ++ tailWord_3189684).sum := by decide
  have hdescent : baseEnd_3189684 < baseStart_3189684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189714 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_3189714 : Nat := 118140960795 + 3189714 * 2 ^ 59
def prefixEnd_3189714 : Nat := 4983230072969 + 3 ^ 40 * 3189714 * 2
def baseEnd_3189714 : Nat := 1091904288250292308670519

theorem tailTrace_3189714 : CollatzResearch.WordTrace tailWord_3189714 prefixEnd_3189714 1091904288250292308670519 := by
  unfold tailWord_3189714
  simp only [CollatzResearch.WordTrace]
  refine ⟨29084606791554603156442049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77558951444145608417178797 29084606791554603156442049)
  ·
    refine ⟨21813455093665952367331537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29084606791554603156442049 21813455093665952367331537)
    ·
      refine ⟨16360091320249464275498653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21813455093665952367331537 16360091320249464275498653)
      ·
        refine ⟨6135034245093549103311995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16360091320249464275498653 6135034245093549103311995)
        ·
          refine ⟨9202551367640323654967993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6135034245093549103311995 9202551367640323654967993)
          ·
            refine ⟨6901913525730242741225995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9202551367640323654967993 6901913525730242741225995)
            ·
              refine ⟨10352870288595364111838993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6901913525730242741225995 10352870288595364111838993)
              ·
                refine ⟨7764652716446523083879245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10352870288595364111838993 7764652716446523083879245)
                ·
                  refine ⟨2911744768667446156454717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7764652716446523083879245 2911744768667446156454717)
                  ·
                    refine ⟨1091904288250292308670519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2911744768667446156454717 1091904288250292308670519)
                    ·
                      rfl

theorem cell22_3189714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_3189714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189714 prefixEnd_3189714 := by exact prefixLift 3189714
  have htrace : WordTrace (prefixWord ++ tailWord_3189714) baseStart_3189714 baseEnd_3189714 := by
    simpa [prefixWord, tailWord_3189714, baseEnd_3189714] using wordTrace_append hprefix tailTrace_3189714
  have hstable : (prefixWord ++ tailWord_3189714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189714).length < 2 ^ (prefixWord ++ tailWord_3189714).sum := by decide
  have hdescent : baseEnd_3189714 < baseStart_3189714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189774 : List Nat := [4, 1, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_3189774 : Nat := 118140960795 + 3189774 * 2 ^ 59
def prefixEnd_3189774 : Nat := 4983230072969 + 3 ^ 40 * 3189774 * 2
def baseEnd_3189774 : Nat := 1091924827476472152170335

theorem tailTrace_3189774 : CollatzResearch.WordTrace tailWord_3189774 prefixEnd_3189774 1091924827476472152170335 := by
  unfold tailWord_3189774
  simp only [CollatzResearch.WordTrace]
  refine ⟨14542576943250130359119047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77560410364000695248634917 14542576943250130359119047)
  ·
    refine ⟨21813865414875195538678571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14542576943250130359119047 21813865414875195538678571)
    ·
      refine ⟨32720798122312793308017857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21813865414875195538678571 32720798122312793308017857)
      ·
        refine ⟨24540598591734594981013393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32720798122312793308017857 24540598591734594981013393)
        ·
          refine ⟨18405448943800946235760045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24540598591734594981013393 18405448943800946235760045)
          ·
            refine ⟨6902043353925354838410017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18405448943800946235760045 6902043353925354838410017)
            ·
              refine ⟨5176532515444016128807513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6902043353925354838410017 5176532515444016128807513)
              ·
                refine ⟨3882399386583012096605635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5176532515444016128807513 3882399386583012096605635)
                ·
                  refine ⟨5823599079874518144908453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3882399386583012096605635 5823599079874518144908453)
                  ·
                    refine ⟨1091924827476472152170335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5823599079874518144908453 1091924827476472152170335)
                    ·
                      rfl

theorem cell22_3189774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_3189774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189774 prefixEnd_3189774 := by exact prefixLift 3189774
  have htrace : WordTrace (prefixWord ++ tailWord_3189774) baseStart_3189774 baseEnd_3189774 := by
    simpa [prefixWord, tailWord_3189774, baseEnd_3189774] using wordTrace_append hprefix tailTrace_3189774
  have hstable : (prefixWord ++ tailWord_3189774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189774).length < 2 ^ (prefixWord ++ tailWord_3189774).sum := by decide
  have hdescent : baseEnd_3189774 < baseStart_3189774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189785 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 1, 6]
def baseStart_3189785 : Nat := 118140960795 + 3189785 * 2 ^ 59
def prefixEnd_3189785 : Nat := 4983230072969 + 3 ^ 40 * 3189785 * 2
def baseEnd_3189785 : Nat := 1091928593001271790145301

theorem tailTrace_3189785 : CollatzResearch.WordTrace tailWord_3189785 prefixEnd_3189785 1091928593001271790145301 := by
  unfold tailWord_3189785
  simp only [CollatzResearch.WordTrace]
  refine ⟨116341016748961191751602809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77560677832640794501068539 116341016748961191751602809)
  ·
    refine ⟨87255762561720893813702107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116341016748961191751602809 87255762561720893813702107)
    ·
      refine ⟨130883643842581340720553161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87255762561720893813702107 130883643842581340720553161)
      ·
        refine ⟨98162732881936005540414871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130883643842581340720553161 98162732881936005540414871)
        ·
          refine ⟨147244099322904008310622307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98162732881936005540414871 147244099322904008310622307)
          ·
            refine ⟨220866148984356012465933461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147244099322904008310622307 220866148984356012465933461)
            ·
              refine ⟨10353100733641688084340631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220866148984356012465933461 10353100733641688084340631)
              ·
                refine ⟨15529651100462532126510947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10353100733641688084340631 15529651100462532126510947)
                ·
                  refine ⟨23294476650693798189766421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15529651100462532126510947 23294476650693798189766421)
                  ·
                    refine ⟨1091928593001271790145301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23294476650693798189766421 1091928593001271790145301)
                    ·
                      rfl

theorem cell22_3189785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_3189785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189785 prefixEnd_3189785 := by exact prefixLift 3189785
  have htrace : WordTrace (prefixWord ++ tailWord_3189785) baseStart_3189785 baseEnd_3189785 := by
    simpa [prefixWord, tailWord_3189785, baseEnd_3189785] using wordTrace_append hprefix tailTrace_3189785
  have hstable : (prefixWord ++ tailWord_3189785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189785).length < 2 ^ (prefixWord ++ tailWord_3189785).sum := by decide
  have hdescent : baseEnd_3189785 < baseStart_3189785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189806 : List Nat := [4, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_3189806 : Nat := 118140960795 + 3189806 * 2 ^ 59
def prefixEnd_3189806 : Nat := 4983230072969 + 3 ^ 40 * 3189806 * 2
def baseEnd_3189806 : Nat := 363978593910144911790079

theorem tailTrace_3189806 : CollatzResearch.WordTrace tailWord_3189806 prefixEnd_3189806 363978593910144911790079 := by
  unfold tailWord_3189806
  simp only [CollatzResearch.WordTrace]
  refine ⟨14542722835235639042264659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77561188454590074892078181 14542722835235639042264659)
  ·
    refine ⟨21814084252853458563396989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14542722835235639042264659 21814084252853458563396989)
    ·
      refine ⟨8180281594820046961273871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21814084252853458563396989 8180281594820046961273871)
      ·
        refine ⟨12270422392230070441910807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8180281594820046961273871 12270422392230070441910807)
        ·
          refine ⟨18405633588345105662866211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12270422392230070441910807 18405633588345105662866211)
          ·
            refine ⟨27608450382517658494299317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18405633588345105662866211 27608450382517658494299317)
            ·
              refine ⟨2588292223361030483840561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27608450382517658494299317 2588292223361030483840561)
              ·
                refine ⟨1941219167520772862880421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2588292223361030483840561 1941219167520772862880421)
                ·
                  refine ⟨363978593910144911790079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1941219167520772862880421 363978593910144911790079)
                  ·
                    rfl

theorem cell22_3189806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_3189806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189806 prefixEnd_3189806 := by exact prefixLift 3189806
  have htrace : WordTrace (prefixWord ++ tailWord_3189806) baseStart_3189806 baseEnd_3189806 := by
    simpa [prefixWord, tailWord_3189806, baseEnd_3189806] using wordTrace_append hprefix tailTrace_3189806
  have hstable : (prefixWord ++ tailWord_3189806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189806).length < 2 ^ (prefixWord ++ tailWord_3189806).sum := by decide
  have hdescent : baseEnd_3189806 < baseStart_3189806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189817 : List Nat := [1, 2, 1, 5, 2, 2, 2, 7]
def baseStart_3189817 : Nat := 118140960795 + 3189817 * 2 ^ 59
def prefixEnd_3189817 : Nat := 4983230072969 + 3 ^ 40 * 3189817 * 2
def baseEnd_3189817 : Nat := 121326616361692708149467

theorem tailTrace_3189817 : CollatzResearch.WordTrace tailWord_3189817 prefixEnd_3189817 121326616361692708149467 := by
  unfold tailWord_3189817
  simp only [CollatzResearch.WordTrace]
  refine ⟨116342183884845261216767705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77561455923230174144511803 116342183884845261216767705)
  ·
    refine ⟨87256637913633945912575779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116342183884845261216767705 87256637913633945912575779)
    ·
      refine ⟨130884956870450918868863669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87256637913633945912575779 130884956870450918868863669)
      ·
        refine ⟨12270464706604773643955969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130884956870450918868863669 12270464706604773643955969)
        ·
          refine ⟨9202848529953580232966977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12270464706604773643955969 9202848529953580232966977)
          ·
            refine ⟨6902136397465185174725233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9202848529953580232966977 6902136397465185174725233)
            ·
              refine ⟨5176602298098888881043925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6902136397465185174725233 5176602298098888881043925)
              ·
                refine ⟨121326616361692708149467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5176602298098888881043925 121326616361692708149467)
                ·
                  rfl

theorem cell22_3189817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 7].length) (baseStart_3189817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189817 prefixEnd_3189817 := by exact prefixLift 3189817
  have htrace : WordTrace (prefixWord ++ tailWord_3189817) baseStart_3189817 baseEnd_3189817 := by
    simpa [prefixWord, tailWord_3189817, baseEnd_3189817] using wordTrace_append hprefix tailTrace_3189817
  have hstable : (prefixWord ++ tailWord_3189817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189817).length < 2 ^ (prefixWord ++ tailWord_3189817).sum := by decide
  have hdescent : baseEnd_3189817 < baseStart_3189817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189821 : List Nat := [1, 4, 1, 3, 1, 2, 4, 1, 2, 3]
def baseStart_3189821 : Nat := 118140960795 + 3189821 * 2 ^ 59
def prefixEnd_3189821 : Nat := 4983230072969 + 3 ^ 40 * 3189821 * 2
def baseEnd_3189821 : Nat := 1091940916536979696245191

theorem tailTrace_3189821 : CollatzResearch.WordTrace tailWord_3189821 prefixEnd_3189821 1091940916536979696245191 := by
  unfold tailWord_3189821
  simp only [CollatzResearch.WordTrace]
  refine ⟨116342329776830769899913317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77561553184553846599942211 116342329776830769899913317)
  ·
    refine ⟨21814186833155769356233747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116342329776830769899913317 21814186833155769356233747)
    ·
      refine ⟨32721280249733654034350621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21814186833155769356233747 32721280249733654034350621)
      ·
        refine ⟨12270480093650120262881483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32721280249733654034350621 12270480093650120262881483)
        ·
          refine ⟨18405720140475180394322225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12270480093650120262881483 18405720140475180394322225)
          ·
            refine ⟨13804290105356385295741669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18405720140475180394322225 13804290105356385295741669)
            ·
              refine ⟨2588304394754322242951563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13804290105356385295741669 2588304394754322242951563)
              ·
                refine ⟨3882456592131483364427345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588304394754322242951563 3882456592131483364427345)
                ·
                  refine ⟨2911842444098612523320509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3882456592131483364427345 2911842444098612523320509)
                  ·
                    refine ⟨1091940916536979696245191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2911842444098612523320509 1091940916536979696245191)
                    ·
                      rfl

theorem cell22_3189821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_3189821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189821 prefixEnd_3189821 := by exact prefixLift 3189821
  have htrace : WordTrace (prefixWord ++ tailWord_3189821) baseStart_3189821 baseEnd_3189821 := by
    simpa [prefixWord, tailWord_3189821, baseEnd_3189821] using wordTrace_append hprefix tailTrace_3189821
  have hstable : (prefixWord ++ tailWord_3189821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189821).length < 2 ^ (prefixWord ++ tailWord_3189821).sum := by decide
  have hdescent : baseEnd_3189821 < baseStart_3189821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189832 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 5, 3]
def baseStart_3189832 : Nat := 118140960795 + 3189832 * 2 ^ 59
def prefixEnd_3189832 : Nat := 4983230072969 + 3 ^ 40 * 3189832 * 2
def baseEnd_3189832 : Nat := 1091944682061779334220157

theorem tailTrace_3189832 : CollatzResearch.WordTrace tailWord_3189832 prefixEnd_3189832 1091944682061779334220157 := by
  unfold tailWord_3189832
  simp only [CollatzResearch.WordTrace]
  refine ⟨58171365489895459389281875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77561820653193945852375833 58171365489895459389281875)
  ·
    refine ⟨87257048234843189083922813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58171365489895459389281875 87257048234843189083922813)
    ·
      refine ⟨32721393088066195906471055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87257048234843189083922813 32721393088066195906471055)
      ·
        refine ⟨49082089632099293859706583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32721393088066195906471055 49082089632099293859706583)
        ·
          refine ⟨73623134448148940789559875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49082089632099293859706583 73623134448148940789559875)
          ·
            refine ⟨110434701672223411184339813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73623134448148940789559875 110434701672223411184339813)
            ·
              refine ⟨20706506563541889597063715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110434701672223411184339813 20706506563541889597063715)
              ·
                refine ⟨31059759845312834395595573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20706506563541889597063715 31059759845312834395595573)
                ·
                  refine ⟨2911852485498078224587085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31059759845312834395595573 2911852485498078224587085)
                  ·
                    refine ⟨1091944682061779334220157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2911852485498078224587085 1091944682061779334220157)
                    ·
                      rfl

theorem cell22_3189832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_3189832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189832 prefixEnd_3189832 := by exact prefixLift 3189832
  have htrace : WordTrace (prefixWord ++ tailWord_3189832) baseStart_3189832 baseEnd_3189832 := by
    simpa [prefixWord, tailWord_3189832, baseEnd_3189832] using wordTrace_append hprefix tailTrace_3189832
  have hstable : (prefixWord ++ tailWord_3189832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189832).length < 2 ^ (prefixWord ++ tailWord_3189832).sum := by decide
  have hdescent : baseEnd_3189832 < baseStart_3189832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189924 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 6]
def baseStart_3189924 : Nat := 118140960795 + 3189924 * 2 ^ 59
def prefixEnd_3189924 : Nat := 4983230072969 + 3 ^ 40 * 3189924 * 2
def baseEnd_3189924 : Nat := 363992058513973920306625

theorem tailTrace_3189924 : CollatzResearch.WordTrace tailWord_3189924 prefixEnd_3189924 363992058513973920306625 := by
  unfold tailWord_3189924
  simp only [CollatzResearch.WordTrace]
  refine ⟨58173043247728809245456413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77564057663638412327275217 58173043247728809245456413)
  ·
    refine ⟨21814891217898303467046155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58173043247728809245456413 21814891217898303467046155)
    ·
      refine ⟨32722336826847455200569233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21814891217898303467046155 32722336826847455200569233)
      ·
        refine ⟨24541752620135591400426925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32722336826847455200569233 24541752620135591400426925)
        ·
          refine ⟨9203157232550846775160097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24541752620135591400426925 9203157232550846775160097)
          ·
            refine ⟨6902367924413135081370073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9203157232550846775160097 6902367924413135081370073)
            ·
              refine ⟨5176775943309851311027555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6902367924413135081370073 5176775943309851311027555)
              ·
                refine ⟨7765163914964776966541333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5176775943309851311027555 7765163914964776966541333)
                ·
                  refine ⟨363992058513973920306625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7765163914964776966541333 363992058513973920306625)
                  ·
                    rfl

theorem cell22_3189924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_3189924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189924 prefixEnd_3189924 := by exact prefixLift 3189924
  have htrace : WordTrace (prefixWord ++ tailWord_3189924) baseStart_3189924 baseEnd_3189924 := by
    simpa [prefixWord, tailWord_3189924, baseEnd_3189924] using wordTrace_append hprefix tailTrace_3189924
  have hstable : (prefixWord ++ tailWord_3189924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189924).length < 2 ^ (prefixWord ++ tailWord_3189924).sum := by decide
  have hdescent : baseEnd_3189924 < baseStart_3189924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189939 : List Nat := [1, 1, 1, 2, 3, 2, 2, 5, 2, 3]
def baseStart_3189939 : Nat := 118140960795 + 3189939 * 2 ^ 59
def prefixEnd_3189939 : Nat := 4983230072969 + 3 ^ 40 * 3189939 * 2
def baseEnd_3189939 : Nat := 1091981310348466721794829

theorem tailTrace_3189939 : CollatzResearch.WordTrace tailWord_3189939 prefixEnd_3189939 1091981310348466721794829 := by
  unfold tailWord_3189939
  simp only [CollatzResearch.WordTrace]
  refine ⟨116346633590403276052708871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77564422393602184035139247 116346633590403276052708871)
  ·
    refine ⟨174519950385604914079063307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116346633590403276052708871 174519950385604914079063307)
    ·
      refine ⟨261779925578407371118594961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174519950385604914079063307 261779925578407371118594961)
      ·
        refine ⟨196334944183805528338946221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261779925578407371118594961 196334944183805528338946221)
        ·
          refine ⟨73625604068927073127104833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196334944183805528338946221 73625604068927073127104833)
          ·
            refine ⟨55219203051695304845328625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73625604068927073127104833 55219203051695304845328625)
            ·
              refine ⟨41414402288771478633996469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55219203051695304845328625 41414402288771478633996469)
              ·
                refine ⟨3882600214572326121937169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41414402288771478633996469 3882600214572326121937169)
                ·
                  refine ⟨2911950160929244591452877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3882600214572326121937169 2911950160929244591452877)
                  ·
                    refine ⟨1091981310348466721794829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2911950160929244591452877 1091981310348466721794829)
                    ·
                      rfl

theorem cell22_3189939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 3].length) (baseStart_3189939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3189939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3189939 prefixEnd_3189939 := by exact prefixLift 3189939
  have htrace : WordTrace (prefixWord ++ tailWord_3189939) baseStart_3189939 baseEnd_3189939 := by
    simpa [prefixWord, tailWord_3189939, baseEnd_3189939] using wordTrace_append hprefix tailTrace_3189939
  have hstable : (prefixWord ++ tailWord_3189939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189939).length < 2 ^ (prefixWord ++ tailWord_3189939).sum := by decide
  have hdescent : baseEnd_3189939 < baseStart_3189939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190044 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_3190044 : Nat := 118140960795 + 3190044 * 2 ^ 59
def prefixEnd_3190044 : Nat := 4983230072969 + 3 ^ 40 * 3190044 * 2
def baseEnd_3190044 : Nat := 1092017253994281447919507

theorem tailTrace_3190044 : CollatzResearch.WordTrace tailWord_3190044 prefixEnd_3190044 1092017253994281447919507 := by
  unfold tailWord_3190044
  simp only [CollatzResearch.WordTrace]
  refine ⟨58175231627511439492640593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77566975503348585990187457 58175231627511439492640593)
  ·
    refine ⟨43631423720633579619480445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58175231627511439492640593 43631423720633579619480445)
    ·
      refine ⟨16361783895237592357305167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43631423720633579619480445 16361783895237592357305167)
      ·
        refine ⟨24542675842856388535957751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16361783895237592357305167 24542675842856388535957751)
        ·
          refine ⟨36814013764284582803936627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24542675842856388535957751 36814013764284582803936627)
          ·
            refine ⟨55221020646426874205904941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36814013764284582803936627 55221020646426874205904941)
            ·
              refine ⟨20707882742410077827214353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55221020646426874205904941 20707882742410077827214353)
              ·
                refine ⟨15530912056807558370410765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20707882742410077827214353 15530912056807558370410765)
                ·
                  refine ⟨5824092021302834388904037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15530912056807558370410765 5824092021302834388904037)
                  ·
                    refine ⟨1092017253994281447919507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5824092021302834388904037 1092017253994281447919507)
                    ·
                      rfl

theorem cell22_3190044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_3190044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190044 prefixEnd_3190044 := by exact prefixLift 3190044
  have htrace : WordTrace (prefixWord ++ tailWord_3190044) baseStart_3190044 baseEnd_3190044 := by
    simpa [prefixWord, tailWord_3190044, baseEnd_3190044] using wordTrace_append hprefix tailTrace_3190044
  have hstable : (prefixWord ++ tailWord_3190044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190044).length < 2 ^ (prefixWord ++ tailWord_3190044).sum := by decide
  have hdescent : baseEnd_3190044 < baseStart_3190044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190074 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_3190074 : Nat := 118140960795 + 3190074 * 2 ^ 59
def prefixEnd_3190074 : Nat := 4983230072969 + 3 ^ 40 * 3190074 * 2
def baseEnd_3190074 : Nat := 1092027523607371369669415

theorem tailTrace_3190074 : CollatzResearch.WordTrace tailWord_3190074 prefixEnd_3190074 1092027523607371369669415 := by
  unfold tailWord_3190074
  simp only [CollatzResearch.WordTrace]
  refine ⟨29087889361228548527218319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77567704963276129405915517 29087889361228548527218319)
  ·
    refine ⟨43631834041842822790827479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29087889361228548527218319 43631834041842822790827479)
    ·
      refine ⟨65447751062764234186241219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43631834041842822790827479 65447751062764234186241219)
      ·
        refine ⟨98171626594146351279361829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65447751062764234186241219 98171626594146351279361829)
        ·
          refine ⟨18407179986402440864880343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98171626594146351279361829 18407179986402440864880343)
          ·
            refine ⟨27610769979603661297320515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18407179986402440864880343 27610769979603661297320515)
            ·
              refine ⟨41416154969405491945980773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27610769979603661297320515 41416154969405491945980773)
              ·
                refine ⟨7765529056763529739871395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41416154969405491945980773 7765529056763529739871395)
                ·
                  refine ⟨11648293585145294609807093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7765529056763529739871395 11648293585145294609807093)
                  ·
                    refine ⟨1092027523607371369669415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11648293585145294609807093 1092027523607371369669415)
                    ·
                      rfl

theorem cell22_3190074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_3190074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190074 prefixEnd_3190074 := by exact prefixLift 3190074
  have htrace : WordTrace (prefixWord ++ tailWord_3190074) baseStart_3190074 baseEnd_3190074 := by
    simpa [prefixWord, tailWord_3190074, baseEnd_3190074] using wordTrace_append hprefix tailTrace_3190074
  have hstable : (prefixWord ++ tailWord_3190074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190074).length < 2 ^ (prefixWord ++ tailWord_3190074).sum := by decide
  have hdescent : baseEnd_3190074 < baseStart_3190074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190076 : List Nat := [2, 2, 2, 2, 1, 3, 1, 5, 4]
def baseStart_3190076 : Nat := 118140960795 + 3190076 * 2 ^ 59
def prefixEnd_3190076 : Nat := 4983230072969 + 3 ^ 40 * 3190076 * 2
def baseEnd_3190076 : Nat := 364009402749414677039803

theorem tailTrace_3190076 : CollatzResearch.WordTrace tailWord_3190076 prefixEnd_3190076 364009402749414677039803 := by
  unfold tailWord_3190076
  simp only [CollatzResearch.WordTrace]
  refine ⟨58175815195453474225223041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77567753593937965633630721 58175815195453474225223041)
  ·
    refine ⟨43631861396590105668917281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58175815195453474225223041 43631861396590105668917281)
    ·
      refine ⟨32723896047442579251687961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43631861396590105668917281 32723896047442579251687961)
      ·
        refine ⟨24542922035581934438765971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32723896047442579251687961 24542922035581934438765971)
        ·
          refine ⟨36814383053372901658148957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24542922035581934438765971 36814383053372901658148957)
          ·
            refine ⟨13805393645014838121805859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36814383053372901658148957 13805393645014838121805859)
            ·
              refine ⟨20708090467522257182708789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13805393645014838121805859 20708090467522257182708789)
              ·
                refine ⟨1941383481330211610878949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20708090467522257182708789 1941383481330211610878949)
                ·
                  refine ⟨364009402749414677039803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1941383481330211610878949 364009402749414677039803)
                  ·
                    rfl

theorem cell22_3190076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_3190076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190076 prefixEnd_3190076 := by exact prefixLift 3190076
  have htrace : WordTrace (prefixWord ++ tailWord_3190076) baseStart_3190076 baseEnd_3190076 := by
    simpa [prefixWord, tailWord_3190076, baseEnd_3190076] using wordTrace_append hprefix tailTrace_3190076
  have hstable : (prefixWord ++ tailWord_3190076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190076).length < 2 ^ (prefixWord ++ tailWord_3190076).sum := by decide
  have hdescent : baseEnd_3190076 < baseStart_3190076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190089 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 2, 4]
def baseStart_3190089 : Nat := 118140960795 + 3190089 * 2 ^ 59
def prefixEnd_3190089 : Nat := 4983230072969 + 3 ^ 40 * 3190089 * 2
def baseEnd_3190089 : Nat := 1092032658413916330544369

theorem tailTrace_3190089 : CollatzResearch.WordTrace tailWord_3190089 prefixEnd_3190089 1092032658413916330544369 := by
  unfold tailWord_3190089
  simp only [CollatzResearch.WordTrace]
  refine ⟨116352104539859851670669321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77568069693239901113779547 116352104539859851670669321)
  ·
    refine ⟨87264078404894888753001991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116352104539859851670669321 87264078404894888753001991)
    ·
      refine ⟨130896117607342333129502987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87264078404894888753001991 130896117607342333129502987)
      ·
        refine ⟨196344176411013499694254481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130896117607342333129502987 196344176411013499694254481)
        ·
          refine ⟨147258132308260124770690861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196344176411013499694254481 147258132308260124770690861)
          ·
            refine ⟨55221799615597546789009073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147258132308260124770690861 55221799615597546789009073)
            ·
              refine ⟨41416349711698160091756805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55221799615597546789009073 41416349711698160091756805)
              ·
                refine ⟨7765565570943405017204401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41416349711698160091756805 7765565570943405017204401)
                ·
                  refine ⟨5824174178207553762903301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7765565570943405017204401 5824174178207553762903301)
                  ·
                    refine ⟨1092032658413916330544369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5824174178207553762903301 1092032658413916330544369)
                    ·
                      rfl

theorem cell22_3190089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_3190089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190089 prefixEnd_3190089 := by exact prefixLift 3190089
  have htrace : WordTrace (prefixWord ++ tailWord_3190089) baseStart_3190089 baseEnd_3190089 := by
    simpa [prefixWord, tailWord_3190089, baseEnd_3190089] using wordTrace_append hprefix tailTrace_3190089
  have hstable : (prefixWord ++ tailWord_3190089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190089).length < 2 ^ (prefixWord ++ tailWord_3190089).sum := by decide
  have hdescent : baseEnd_3190089 < baseStart_3190089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190149 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 7]
def baseStart_3190149 : Nat := 118140960795 + 3190149 * 2 ^ 59
def prefixEnd_3190149 : Nat := 4983230072969 + 3 ^ 40 * 3190149 * 2
def baseEnd_3190149 : Nat := 364017732546698724681395

theorem tailTrace_3190149 : CollatzResearch.WordTrace tailWord_3190149 prefixEnd_3190149 364017732546698724681395 := by
  unfold tailWord_3190149
  simp only [CollatzResearch.WordTrace]
  refine ⟨116354292919642481917853501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77569528613094987945235667 116354292919642481917853501)
  ·
    refine ⟨43632859844865930719195063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116354292919642481917853501 43632859844865930719195063)
    ·
      refine ⟨65449289767298896078792595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43632859844865930719195063 65449289767298896078792595)
      ·
        refine ⟨98173934650948344118188893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65449289767298896078792595 98173934650948344118188893)
        ·
          refine ⟨36815225494105629044320835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98173934650948344118188893 36815225494105629044320835)
          ·
            refine ⟨55222838241158443566481253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36815225494105629044320835 55222838241158443566481253)
            ·
              refine ⟨10354282170217208168715235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55222838241158443566481253 10354282170217208168715235)
              ·
                refine ⟨15531423255325812253072853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10354282170217208168715235 15531423255325812253072853)
                ·
                  refine ⟨364017732546698724681395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15531423255325812253072853 364017732546698724681395)
                  ·
                    rfl

theorem cell22_3190149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_3190149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190149 prefixEnd_3190149 := by exact prefixLift 3190149
  have htrace : WordTrace (prefixWord ++ tailWord_3190149) baseStart_3190149 baseEnd_3190149 := by
    simpa [prefixWord, tailWord_3190149, baseEnd_3190149] using wordTrace_append hprefix tailTrace_3190149
  have hstable : (prefixWord ++ tailWord_3190149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190149).length < 2 ^ (prefixWord ++ tailWord_3190149).sum := by decide
  have hdescent : baseEnd_3190149 < baseStart_3190149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190194 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 10]
def baseStart_3190194 : Nat := 118140960795 + 3190194 * 2 ^ 59
def prefixEnd_3190194 : Nat := 4983230072969 + 3 ^ 40 * 3190194 * 2
def baseEnd_3190194 : Nat := 364022867353243685556349

theorem tailTrace_3190194 : CollatzResearch.WordTrace tailWord_3190194 prefixEnd_3190194 364022867353243685556349 := by
  unfold tailWord_3190194
  simp only [CollatzResearch.WordTrace]
  refine ⟨29088983551119863650810409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77570622802986303068827757 29088983551119863650810409)
  ·
    refine ⟨21816737663339897738107807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29088983551119863650810409 21816737663339897738107807)
    ·
      refine ⟨32725106495009846607161711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21816737663339897738107807 32725106495009846607161711)
      ·
        refine ⟨49087659742514769910742567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32725106495009846607161711 49087659742514769910742567)
        ·
          refine ⟨73631489613772154866113851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49087659742514769910742567 73631489613772154866113851)
          ·
            refine ⟨110447234420658232299170777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73631489613772154866113851 110447234420658232299170777)
            ·
              refine ⟨82835425815493674224378083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110447234420658232299170777 82835425815493674224378083)
              ·
                refine ⟨124253138723240511336567125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82835425815493674224378083 124253138723240511336567125)
                ·
                  refine ⟨364022867353243685556349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 124253138723240511336567125 364022867353243685556349)
                  ·
                    rfl

theorem cell22_3190194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_3190194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190194 prefixEnd_3190194 := by exact prefixLift 3190194
  have htrace : WordTrace (prefixWord ++ tailWord_3190194) baseStart_3190194 baseEnd_3190194 := by
    simpa [prefixWord, tailWord_3190194, baseEnd_3190194] using wordTrace_append hprefix tailTrace_3190194
  have hstable : (prefixWord ++ tailWord_3190194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190194).length < 2 ^ (prefixWord ++ tailWord_3190194).sum := by decide
  have hdescent : baseEnd_3190194 < baseStart_3190194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190204 : List Nat := [2, 2, 2, 4, 2, 2, 2, 2, 1, 3]
def baseStart_3190204 : Nat := 118140960795 + 3190204 * 2 ^ 59
def prefixEnd_3190204 : Nat := 4983230072969 + 3 ^ 40 * 3190204 * 2
def baseEnd_3190204 : Nat := 1092072025264094363919017

theorem tailTrace_3190204 : CollatzResearch.WordTrace tailWord_3190204 prefixEnd_3190204 1092072025264094363919017 := by
  unfold tailWord_3190204
  simp only [CollatzResearch.WordTrace]
  refine ⟨58178149467221613155552833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77570865956295484207403777 58178149467221613155552833)
  ·
    refine ⟨43633612100416209866664625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58178149467221613155552833 43633612100416209866664625)
    ·
      refine ⟨32725209075312157399998469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43633612100416209866664625 32725209075312157399998469)
      ·
        refine ⟨6135976701621029512499713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32725209075312157399998469 6135976701621029512499713)
        ·
          refine ⟨4601982526215772134374785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6135976701621029512499713 4601982526215772134374785)
          ·
            refine ⟨3451486894661829100781089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4601982526215772134374785 3451486894661829100781089)
            ·
              refine ⟨2588615170996371825585817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3451486894661829100781089 2588615170996371825585817)
              ·
                refine ⟨1941461378247278869189363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2588615170996371825585817 1941461378247278869189363)
                ·
                  refine ⟨2912192067370918303784045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941461378247278869189363 2912192067370918303784045)
                  ·
                    refine ⟨1092072025264094363919017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2912192067370918303784045 1092072025264094363919017)
                    ·
                      rfl

theorem cell22_3190204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_3190204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190204 prefixEnd_3190204 := by exact prefixLift 3190204
  have htrace : WordTrace (prefixWord ++ tailWord_3190204) baseStart_3190204 baseEnd_3190204 := by
    simpa [prefixWord, tailWord_3190204, baseEnd_3190204] using wordTrace_append hprefix tailTrace_3190204
  have hstable : (prefixWord ++ tailWord_3190204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190204).length < 2 ^ (prefixWord ++ tailWord_3190204).sum := by decide
  have hdescent : baseEnd_3190204 < baseStart_3190204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190224 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 3, 6]
def baseStart_3190224 : Nat := 118140960795 + 3190224 * 2 ^ 59
def prefixEnd_3190224 : Nat := 4983230072969 + 3 ^ 40 * 3190224 * 2
def baseEnd_3190224 : Nat := 1092078871672820978418955

theorem tailTrace_3190224 : CollatzResearch.WordTrace tailWord_3190224 prefixEnd_3190224 1092078871672820978418955 := by
  unfold tailWord_3190224
  simp only [CollatzResearch.WordTrace]
  refine ⟨58178514197185384863416863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77571352262913846484555817 58178514197185384863416863)
  ·
    refine ⟨87267771295778077295125295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58178514197185384863416863 87267771295778077295125295)
    ·
      refine ⟨130901656943667115942687943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87267771295778077295125295 130901656943667115942687943)
      ·
        refine ⟨196352485415500673914031915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130901656943667115942687943 196352485415500673914031915)
        ·
          refine ⟨294528728123251010871047873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196352485415500673914031915 294528728123251010871047873)
          ·
            refine ⟨220896546092438258153285905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294528728123251010871047873 220896546092438258153285905)
            ·
              refine ⟨165672409569328693614964429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220896546092438258153285905 165672409569328693614964429)
              ·
                refine ⟨62127153588498260105611661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165672409569328693614964429 62127153588498260105611661)
                ·
                  refine ⟨23297682595686847539604373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62127153588498260105611661 23297682595686847539604373)
                  ·
                    refine ⟨1092078871672820978418955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23297682595686847539604373 1092078871672820978418955)
                    ·
                      rfl

theorem cell22_3190224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_3190224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190224 prefixEnd_3190224 := by exact prefixLift 3190224
  have htrace : WordTrace (prefixWord ++ tailWord_3190224) baseStart_3190224 baseEnd_3190224 := by
    simpa [prefixWord, tailWord_3190224, baseEnd_3190224] using wordTrace_append hprefix tailTrace_3190224
  have hstable : (prefixWord ++ tailWord_3190224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190224).length < 2 ^ (prefixWord ++ tailWord_3190224).sum := by decide
  have hdescent : baseEnd_3190224 < baseStart_3190224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190228 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 6]
def baseStart_3190228 : Nat := 118140960795 + 3190228 * 2 ^ 59
def prefixEnd_3190228 : Nat := 4983230072969 + 3 ^ 40 * 3190228 * 2
def baseEnd_3190228 : Nat := 364026746984855433772981

theorem tailTrace_3190228 : CollatzResearch.WordTrace tailWord_3190228 prefixEnd_3190228 364026746984855433772981 := by
  unfold tailWord_3190228
  simp only [CollatzResearch.WordTrace]
  refine ⟨58178587143178139204989669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77571449524237518939986225 58178587143178139204989669)
  ·
    refine ⟨10908485089345901100935563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58178587143178139204989669 10908485089345901100935563)
    ·
      refine ⟨16362727634018851651403345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10908485089345901100935563 16362727634018851651403345)
      ·
        refine ⟨12272045725514138738552509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16362727634018851651403345 12272045725514138738552509)
        ·
          refine ⟨4602017147067802026957191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12272045725514138738552509 4602017147067802026957191)
          ·
            refine ⟨6903025720601703040435787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4602017147067802026957191 6903025720601703040435787)
            ·
              refine ⟨10354538580902554560653681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6903025720601703040435787 10354538580902554560653681)
              ·
                refine ⟨7765903935676915920490261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10354538580902554560653681 7765903935676915920490261)
                ·
                  refine ⟨364026746984855433772981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7765903935676915920490261 364026746984855433772981)
                  ·
                    rfl

theorem cell22_3190228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_3190228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190228 prefixEnd_3190228 := by exact prefixLift 3190228
  have htrace : WordTrace (prefixWord ++ tailWord_3190228) baseStart_3190228 baseEnd_3190228 := by
    simpa [prefixWord, tailWord_3190228, baseEnd_3190228] using wordTrace_append hprefix tailTrace_3190228
  have hstable : (prefixWord ++ tailWord_3190228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190228).length < 2 ^ (prefixWord ++ tailWord_3190228).sum := by decide
  have hdescent : baseEnd_3190228 < baseStart_3190228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190241 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 1, 6]
def baseStart_3190241 : Nat := 118140960795 + 3190241 * 2 ^ 59
def prefixEnd_3190241 : Nat := 4983230072969 + 3 ^ 40 * 3190241 * 2
def baseEnd_3190241 : Nat := 1092084691120238600743903

theorem tailTrace_3190241 : CollatzResearch.WordTrace tailWord_3190241 prefixEnd_3190241 1092084691120238600743903 := by
  unfold tailWord_3190241
  simp only [CollatzResearch.WordTrace]
  refine ⟨116357648435309181630202577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77571765623539454420135051 116357648435309181630202577)
  ·
    refine ⟨87268236326481886222651933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116357648435309181630202577 87268236326481886222651933)
    ·
      refine ⟨32725588622430707333494475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87268236326481886222651933 32725588622430707333494475)
      ·
        refine ⟨49088382933646061000241713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32725588622430707333494475 49088382933646061000241713)
        ·
          refine ⟨36816287200234545750181285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49088382933646061000241713 36816287200234545750181285)
          ·
            refine ⟨6903053850043977328158991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36816287200234545750181285 6903053850043977328158991)
            ·
              refine ⟨10354580775065965992238487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6903053850043977328158991 10354580775065965992238487)
              ·
                refine ⟨15531871162598948988357731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10354580775065965992238487 15531871162598948988357731)
                ·
                  refine ⟨23297806743898423482536597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15531871162598948988357731 23297806743898423482536597)
                  ·
                    refine ⟨1092084691120238600743903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23297806743898423482536597 1092084691120238600743903)
                    ·
                      rfl

theorem cell22_3190241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_3190241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190241 prefixEnd_3190241 := by exact prefixLift 3190241
  have htrace : WordTrace (prefixWord ++ tailWord_3190241) baseStart_3190241 baseEnd_3190241 := by
    simpa [prefixWord, tailWord_3190241, baseEnd_3190241] using wordTrace_append hprefix tailTrace_3190241
  have hstable : (prefixWord ++ tailWord_3190241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190241).length < 2 ^ (prefixWord ++ tailWord_3190241).sum := by decide
  have hdescent : baseEnd_3190241 < baseStart_3190241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190245 : List Nat := [1, 3, 1, 5, 1, 2, 2, 3, 4]
def baseStart_3190245 : Nat := 118140960795 + 3190245 * 2 ^ 59
def prefixEnd_3190245 : Nat := 4983230072969 + 3 ^ 40 * 3190245 * 2
def baseEnd_3190245 : Nat := 364028686800661307881297

theorem tailTrace_3190245 : CollatzResearch.WordTrace tailWord_3190245 prefixEnd_3190245 364028686800661307881297 := by
  unfold tailWord_3190245
  simp only [CollatzResearch.WordTrace]
  refine ⟨116357794327294690313348189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77571862884863126875565459 116357794327294690313348189)
  ·
    refine ⟨43634172872735508867505571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116357794327294690313348189 43634172872735508867505571)
    ·
      refine ⟨65451259309103263301258357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43634172872735508867505571 65451259309103263301258357)
      ·
        refine ⟨6136055560228430934492971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65451259309103263301258357 6136055560228430934492971)
        ·
          refine ⟨9204083340342646401739457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6136055560228430934492971 9204083340342646401739457)
          ·
            refine ⟨6903062505256984801304593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9204083340342646401739457 6903062505256984801304593)
            ·
              refine ⟨5177296878942738600978445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6903062505256984801304593 5177296878942738600978445)
              ·
                refine ⟨1941486329603526975366917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5177296878942738600978445 1941486329603526975366917)
                ·
                  refine ⟨364028686800661307881297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1941486329603526975366917 364028686800661307881297)
                  ·
                    rfl

theorem cell22_3190245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_3190245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190245 prefixEnd_3190245 := by exact prefixLift 3190245
  have htrace : WordTrace (prefixWord ++ tailWord_3190245) baseStart_3190245 baseEnd_3190245 := by
    simpa [prefixWord, tailWord_3190245, baseEnd_3190245] using wordTrace_append hprefix tailTrace_3190245
  have hstable : (prefixWord ++ tailWord_3190245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190245).length < 2 ^ (prefixWord ++ tailWord_3190245).sum := by decide
  have hdescent : baseEnd_3190245 < baseStart_3190245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190301 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 9]
def baseStart_3190301 : Nat := 118140960795 + 3190301 * 2 ^ 59
def prefixEnd_3190301 : Nat := 4983230072969 + 3 ^ 40 * 3190301 * 2
def baseEnd_3190301 : Nat := 364035076782139481414573

theorem tailTrace_3190301 : CollatzResearch.WordTrace tailWord_3190301 prefixEnd_3190301 364035076782139481414573 := by
  unfold tailWord_3190301
  simp only [CollatzResearch.WordTrace]
  refine ⟨116359836815091811877386757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77573224543394541251591171 116359836815091811877386757)
  ·
    refine ⟨21817469402829714727010017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116359836815091811877386757 21817469402829714727010017)
    ·
      refine ⟨16363102052122286045257513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21817469402829714727010017 16363102052122286045257513)
      ·
        refine ⟨12272326539091714533943135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16363102052122286045257513 12272326539091714533943135)
        ·
          refine ⟨18408489808637571800914703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12272326539091714533943135 18408489808637571800914703)
          ·
            refine ⟨27612734712956357701372055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18408489808637571800914703 27612734712956357701372055)
            ·
              refine ⟨41419102069434536552058083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27612734712956357701372055 41419102069434536552058083)
              ·
                refine ⟨62128653104151804828087125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41419102069434536552058083 62128653104151804828087125)
                ·
                  refine ⟨364035076782139481414573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62128653104151804828087125 364035076782139481414573)
                  ·
                    rfl

theorem cell22_3190301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_3190301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190301 prefixEnd_3190301 := by exact prefixLift 3190301
  have htrace : WordTrace (prefixWord ++ tailWord_3190301) baseStart_3190301 baseEnd_3190301 := by
    simpa [prefixWord, tailWord_3190301, baseEnd_3190301] using wordTrace_append hprefix tailTrace_3190301
  have hstable : (prefixWord ++ tailWord_3190301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190301).length < 2 ^ (prefixWord ++ tailWord_3190301).sum := by decide
  have hdescent : baseEnd_3190301 < baseStart_3190301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190318 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_3190318 : Nat := 118140960795 + 3190318 * 2 ^ 59
def prefixEnd_3190318 : Nat := 4983230072969 + 3 ^ 40 * 3190318 * 2
def baseEnd_3190318 : Nat := 364037016597945355522889

theorem tailTrace_3190318 : CollatzResearch.WordTrace tailWord_3190318 prefixEnd_3190318 364037016597945355522889 := by
  unfold tailWord_3190318
  simp only [CollatzResearch.WordTrace]
  refine ⟨14545057107003777972594451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77573637904020149187170405 14545057107003777972594451)
  ·
    refine ⟨21817585660505666958891677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14545057107003777972594451 21817585660505666958891677)
    ·
      refine ⟨8181594622689625109584379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21817585660505666958891677 8181594622689625109584379)
      ·
        refine ⟨12272391934034437664376569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8181594622689625109584379 12272391934034437664376569)
        ·
          refine ⟨9204293950525828248282427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12272391934034437664376569 9204293950525828248282427)
          ·
            refine ⟨13806440925788742372423641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9204293950525828248282427 13806440925788742372423641)
            ·
              refine ⟨10354830694341556779317731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13806440925788742372423641 10354830694341556779317731)
              ·
                refine ⟨15532246041512335168976597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10354830694341556779317731 15532246041512335168976597)
                ·
                  refine ⟨364037016597945355522889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15532246041512335168976597 364037016597945355522889)
                  ·
                    rfl

theorem cell22_3190318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_3190318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190318 prefixEnd_3190318 := by exact prefixLift 3190318
  have htrace : WordTrace (prefixWord ++ tailWord_3190318) baseStart_3190318 baseEnd_3190318 := by
    simpa [prefixWord, tailWord_3190318, baseEnd_3190318] using wordTrace_append hprefix tailTrace_3190318
  have hstable : (prefixWord ++ tailWord_3190318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190318).length < 2 ^ (prefixWord ++ tailWord_3190318).sum := by decide
  have hdescent : baseEnd_3190318 < baseStart_3190318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190335 : List Nat := [1, 1, 2, 2, 3, 5, 2, 1, 5]
def baseStart_3190335 : Nat := 118140960795 + 3190335 * 2 ^ 59
def prefixEnd_3190335 : Nat := 4983230072969 + 3 ^ 40 * 3190335 * 2
def baseEnd_3190335 : Nat := 364038956413751229631205

theorem tailTrace_3190335 : CollatzResearch.WordTrace tailWord_3190335 prefixEnd_3190335 364038956413751229631205 := by
  unfold tailWord_3190335
  simp only [CollatzResearch.WordTrace]
  refine ⟨116361076896968635684124459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77574051264645757122749639 116361076896968635684124459)
  ·
    refine ⟨174541615345452953526186689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116361076896968635684124459 174541615345452953526186689)
    ·
      refine ⟨130906211509089715144640017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174541615345452953526186689 130906211509089715144640017)
      ·
        refine ⟨98179658631817286358480013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130906211509089715144640017 98179658631817286358480013)
        ·
          refine ⟨36817371986931482384430005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98179658631817286358480013 36817371986931482384430005)
          ·
            refine ⟨3451628623774826473540313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36817371986931482384430005 3451628623774826473540313)
            ·
              refine ⟨2588721467831119855155235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3451628623774826473540313 2588721467831119855155235)
              ·
                refine ⟨3883082201746679782732853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588721467831119855155235 3883082201746679782732853)
                ·
                  refine ⟨364038956413751229631205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3883082201746679782732853 364038956413751229631205)
                  ·
                    rfl

theorem cell22_3190335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 5].length) (baseStart_3190335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190335 prefixEnd_3190335 := by exact prefixLift 3190335
  have htrace : WordTrace (prefixWord ++ tailWord_3190335) baseStart_3190335 baseEnd_3190335 := by
    simpa [prefixWord, tailWord_3190335, baseEnd_3190335] using wordTrace_append hprefix tailTrace_3190335
  have hstable : (prefixWord ++ tailWord_3190335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190335).length < 2 ^ (prefixWord ++ tailWord_3190335).sum := by decide
  have hdescent : baseEnd_3190335 < baseStart_3190335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190346 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 8]
def baseStart_3190346 : Nat := 118140960795 + 3190346 * 2 ^ 59
def prefixEnd_3190346 : Nat := 4983230072969 + 3 ^ 40 * 3190346 * 2
def baseEnd_3190346 : Nat := 364040211588684442289527

theorem tailTrace_3190346 : CollatzResearch.WordTrace tailWord_3190346 prefixEnd_3190346 364040211588684442289527 := by
  unfold tailWord_3190346
  simp only [CollatzResearch.WordTrace]
  refine ⟨29090369524982196140693723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77574318733285856375183261 29090369524982196140693723)
  ·
    refine ⟨43635554287473294211040585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29090369524982196140693723 43635554287473294211040585)
    ·
      refine ⟨32726665715604970658280439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43635554287473294211040585 32726665715604970658280439)
      ·
        refine ⟨49089998573407455987420659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32726665715604970658280439 49089998573407455987420659)
        ·
          refine ⟨73634997860111183981130989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49089998573407455987420659 73634997860111183981130989)
          ·
            refine ⟨27613124197541693992924121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73634997860111183981130989 27613124197541693992924121)
            ·
              refine ⟨20709843148156270494693091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27613124197541693992924121 20709843148156270494693091)
              ·
                refine ⟨31064764722234405742039637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20709843148156270494693091 31064764722234405742039637)
                ·
                  refine ⟨364040211588684442289527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31064764722234405742039637 364040211588684442289527)
                  ·
                    rfl

theorem cell22_3190346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_3190346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190346 prefixEnd_3190346 := by exact prefixLift 3190346
  have htrace : WordTrace (prefixWord ++ tailWord_3190346) baseStart_3190346 baseEnd_3190346 := by
    simpa [prefixWord, tailWord_3190346, baseEnd_3190346] using wordTrace_append hprefix tailTrace_3190346
  have hstable : (prefixWord ++ tailWord_3190346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190346).length < 2 ^ (prefixWord ++ tailWord_3190346).sum := by decide
  have hdescent : baseEnd_3190346 < baseStart_3190346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190348 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_3190348 : Nat := 118140960795 + 3190348 * 2 ^ 59
def prefixEnd_3190348 : Nat := 4983230072969 + 3 ^ 40 * 3190348 * 2
def baseEnd_3190348 : Nat := 1092121319406925988318575

theorem tailTrace_3190348 : CollatzResearch.WordTrace tailWord_3190348 prefixEnd_3190348 1092121319406925988318575 := by
  unfold tailWord_3190348
  simp only [CollatzResearch.WordTrace]
  refine ⟨58180775522960769452173849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77574367363947692602898465 58180775522960769452173849)
  ·
    refine ⟨43635581642220577089130387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58180775522960769452173849 43635581642220577089130387)
    ·
      refine ⟨65453372463330865633695581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43635581642220577089130387 65453372463330865633695581)
      ·
        refine ⟨24545014673749074612635843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65453372463330865633695581 24545014673749074612635843)
        ·
          refine ⟨36817522010623611918953765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24545014673749074612635843 36817522010623611918953765)
          ·
            refine ⟨6903285376991927234803831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36817522010623611918953765 6903285376991927234803831)
            ·
              refine ⟨10354928065487890852205747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6903285376991927234803831 10354928065487890852205747)
              ·
                refine ⟨15532392098231836278308621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10354928065487890852205747 15532392098231836278308621)
                ·
                  refine ⟨5824647036836938604365733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15532392098231836278308621 5824647036836938604365733)
                  ·
                    refine ⟨1092121319406925988318575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5824647036836938604365733 1092121319406925988318575)
                    ·
                      rfl

theorem cell22_3190348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_3190348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190348 prefixEnd_3190348 := by exact prefixLift 3190348
  have htrace : WordTrace (prefixWord ++ tailWord_3190348) baseStart_3190348 baseEnd_3190348 := by
    simpa [prefixWord, tailWord_3190348, baseEnd_3190348] using wordTrace_append hprefix tailTrace_3190348
  have hstable : (prefixWord ++ tailWord_3190348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190348).length < 2 ^ (prefixWord ++ tailWord_3190348).sum := by decide
  have hdescent : baseEnd_3190348 < baseStart_3190348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190410 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 2, 4]
def baseStart_3190410 : Nat := 118140960795 + 3190410 * 2 ^ 59
def prefixEnd_3190410 : Nat := 4983230072969 + 3 ^ 40 * 3190410 * 2
def baseEnd_3190410 : Nat := 1092142543273978493268385

theorem tailTrace_3190410 : CollatzResearch.WordTrace tailWord_3190410 prefixEnd_3190410 1092142543273978493268385 := by
  unfold tailWord_3190410
  simp only [CollatzResearch.WordTrace]
  refine ⟨29090953092924230873276171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77575874914464615662069789 29090953092924230873276171)
  ·
    refine ⟨43636429639386346309914257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29090953092924230873276171 43636429639386346309914257)
    ·
      refine ⟨32727322229539759732435693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43636429639386346309914257 32727322229539759732435693)
      ·
        refine ⟨12272745836077409899663385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32727322229539759732435693 12272745836077409899663385)
        ·
          refine ⟨9204559377058057424747539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12272745836077409899663385 9204559377058057424747539)
          ·
            refine ⟨13806839065587086137121309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9204559377058057424747539 13806839065587086137121309)
            ·
              refine ⟨5177564649595157301420491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13806839065587086137121309 5177564649595157301420491)
              ·
                refine ⟨7766346974392735952130737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5177564649595157301420491 7766346974392735952130737)
                ·
                  refine ⟨5824760230794551964098053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7766346974392735952130737 5824760230794551964098053)
                  ·
                    refine ⟨1092142543273978493268385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5824760230794551964098053 1092142543273978493268385)
                    ·
                      rfl

theorem cell22_3190410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_3190410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190410 prefixEnd_3190410 := by exact prefixLift 3190410
  have htrace : WordTrace (prefixWord ++ tailWord_3190410) baseStart_3190410 baseEnd_3190410 := by
    simpa [prefixWord, tailWord_3190410, baseEnd_3190410] using wordTrace_append hprefix tailTrace_3190410
  have hstable : (prefixWord ++ tailWord_3190410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190410).length < 2 ^ (prefixWord ++ tailWord_3190410).sum := by decide
  have hdescent : baseEnd_3190410 < baseStart_3190410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190446 : List Nat := [4, 1, 4, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3190446 : Nat := 118140960795 + 3190446 * 2 ^ 59
def prefixEnd_3190446 : Nat := 4983230072969 + 3 ^ 40 * 3190446 * 2
def baseEnd_3190446 : Nat := 1092154866809686399368275

theorem tailTrace_3190446 : CollatzResearch.WordTrace tailWord_3190446 prefixEnd_3190446 1092154866809686399368275 := by
  unfold tailWord_3190446
  simp only [CollatzResearch.WordTrace]
  refine ⟨14545640674945812705176899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77576750266377667760943461 14545640674945812705176899)
  ·
    refine ⟨21818461012418719057765349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14545640674945812705176899 21818461012418719057765349)
    ·
      refine ⟨4090961439828509823331003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21818461012418719057765349 4090961439828509823331003)
      ·
        refine ⟨6136442159742764734996505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4090961439828509823331003 6136442159742764734996505)
        ·
          refine ⟨4602331619807073551247379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6136442159742764734996505 4602331619807073551247379)
          ·
            refine ⟨6903497429710610326871069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4602331619807073551247379 6903497429710610326871069)
            ·
              refine ⟨2588811536141478872576651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6903497429710610326871069 2588811536141478872576651)
              ·
                refine ⟨3883217304212218308864977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588811536141478872576651 3883217304212218308864977)
                ·
                  refine ⟨2912412978159163731648733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3883217304212218308864977 2912412978159163731648733)
                  ·
                    refine ⟨1092154866809686399368275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2912412978159163731648733 1092154866809686399368275)
                    ·
                      rfl

theorem cell22_3190446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3190446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190446 prefixEnd_3190446 := by exact prefixLift 3190446
  have htrace : WordTrace (prefixWord ++ tailWord_3190446) baseStart_3190446 baseEnd_3190446 := by
    simpa [prefixWord, tailWord_3190446, baseEnd_3190446] using wordTrace_append hprefix tailTrace_3190446
  have hstable : (prefixWord ++ tailWord_3190446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190446).length < 2 ^ (prefixWord ++ tailWord_3190446).sum := by decide
  have hdescent : baseEnd_3190446 < baseStart_3190446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190528 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 6, 4]
def baseStart_3190528 : Nat := 118140960795 + 3190528 * 2 ^ 59
def prefixEnd_3190528 : Nat := 4983230072969 + 3 ^ 40 * 3190528 * 2
def baseEnd_3190528 : Nat := 1092182937085465518818023

theorem tailTrace_3190528 : CollatzResearch.WordTrace tailWord_3190528 prefixEnd_3190528 1092182937085465518818023 := by
  unfold tailWord_3190528
  simp only [CollatzResearch.WordTrace]
  refine ⟨58184058092634714822950119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77578744123512953097266825 58184058092634714822950119)
  ·
    refine ⟨87276087138952072234425179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58184058092634714822950119 87276087138952072234425179)
    ·
      refine ⟨130914130708428108351637769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87276087138952072234425179 130914130708428108351637769)
      ·
        refine ⟨98185598031321081263728327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130914130708428108351637769 98185598031321081263728327)
        ·
          refine ⟨147278397046981621895592491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98185598031321081263728327 147278397046981621895592491)
          ·
            refine ⟨220917595570472432843388737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147278397046981621895592491 220917595570472432843388737)
            ·
              refine ⟨165688196677854324632541553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220917595570472432843388737 165688196677854324632541553)
              ·
                refine ⟨124266147508390743474406165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165688196677854324632541553 124266147508390743474406165)
                ·
                  refine ⟨5824975664455816100362789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124266147508390743474406165 5824975664455816100362789)
                  ·
                    refine ⟨1092182937085465518818023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5824975664455816100362789 1092182937085465518818023)
                    ·
                      rfl

theorem cell22_3190528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_3190528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190528 prefixEnd_3190528 := by exact prefixLift 3190528
  have htrace : WordTrace (prefixWord ++ tailWord_3190528) baseStart_3190528 baseEnd_3190528 := by
    simpa [prefixWord, tailWord_3190528, baseEnd_3190528] using wordTrace_append hprefix tailTrace_3190528
  have hstable : (prefixWord ++ tailWord_3190528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190528).length < 2 ^ (prefixWord ++ tailWord_3190528).sum := by decide
  have hdescent : baseEnd_3190528 < baseStart_3190528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190549 : List Nat := [1, 3, 2, 1, 2, 5, 2, 2, 4]
def baseStart_3190549 : Nat := 118140960795 + 3190549 * 2 ^ 59
def prefixEnd_3190549 : Nat := 4983230072969 + 3 ^ 40 * 3190549 * 2
def baseEnd_3190549 : Nat := 364063375271542821347653

theorem tailTrace_3190549 : CollatzResearch.WordTrace tailWord_3190549 prefixEnd_3190549 364063375271542821347653 := by
  unfold tailWord_3190549
  simp only [CollatzResearch.WordTrace]
  refine ⟨116368882118193350232414701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77579254745462233488276467 116368882118193350232414701)
  ·
    refine ⟨43638330794322506337155513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116368882118193350232414701 43638330794322506337155513)
    ·
      refine ⟨32728748095741879752866635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43638330794322506337155513 32728748095741879752866635)
      ·
        refine ⟨49093122143612819629299953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32728748095741879752866635 49093122143612819629299953)
        ·
          refine ⟨36819841607709614721974965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49093122143612819629299953 36819841607709614721974965)
          ·
            refine ⟨3451860150722776380185153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36819841607709614721974965 3451860150722776380185153)
            ·
              refine ⟨2588895113042082285138865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3451860150722776380185153 2588895113042082285138865)
              ·
                refine ⟨1941671334781561713854149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2588895113042082285138865 1941671334781561713854149)
                ·
                  refine ⟨364063375271542821347653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1941671334781561713854149 364063375271542821347653)
                  ·
                    rfl

theorem cell22_3190549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_3190549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190549 prefixEnd_3190549 := by exact prefixLift 3190549
  have htrace : WordTrace (prefixWord ++ tailWord_3190549) baseStart_3190549 baseEnd_3190549 := by
    simpa [prefixWord, tailWord_3190549, baseEnd_3190549] using wordTrace_append hprefix tailTrace_3190549
  have hstable : (prefixWord ++ tailWord_3190549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190549).length < 2 ^ (prefixWord ++ tailWord_3190549).sum := by decide
  have hdescent : baseEnd_3190549 < baseStart_3190549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190575 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 3, 3]
def baseStart_3190575 : Nat := 118140960795 + 3190575 * 2 ^ 59
def prefixEnd_3190575 : Nat := 4983230072969 + 3 ^ 40 * 3190575 * 2
def baseEnd_3190575 : Nat := 1092199026145973062892879

theorem tailTrace_3190575 : CollatzResearch.WordTrace tailWord_3190575 prefixEnd_3190575 1092199026145973062892879 := by
  unfold tailWord_3190575
  simp only [CollatzResearch.WordTrace]
  refine ⟨116369830416099156672861179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77579886944066104448574119 116369830416099156672861179)
  ·
    refine ⟨174554745624148735009291769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116369830416099156672861179 174554745624148735009291769)
    ·
      refine ⟨130916059218111551256968827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174554745624148735009291769 130916059218111551256968827)
      ·
        refine ⟨196374088827167326885453241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130916059218111551256968827 196374088827167326885453241)
        ·
          refine ⟨147280566620375495164089931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196374088827167326885453241 147280566620375495164089931)
          ·
            refine ⟨220920849930563242746134897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147280566620375495164089931 220920849930563242746134897)
            ·
              refine ⟨165690637447922432059601173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220920849930563242746134897 165690637447922432059601173)
              ·
                refine ⟨7766748630371364002793805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165690637447922432059601173 7766748630371364002793805)
                ·
                  refine ⟨2912530736389261501047677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7766748630371364002793805 2912530736389261501047677)
                  ·
                    refine ⟨1092199026145973062892879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2912530736389261501047677 1092199026145973062892879)
                    ·
                      rfl

theorem cell22_3190575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 3].length) (baseStart_3190575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190575 prefixEnd_3190575 := by exact prefixLift 3190575
  have htrace : WordTrace (prefixWord ++ tailWord_3190575) baseStart_3190575 baseEnd_3190575 := by
    simpa [prefixWord, tailWord_3190575, baseEnd_3190575] using wordTrace_append hprefix tailTrace_3190575
  have hstable : (prefixWord ++ tailWord_3190575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190575).length < 2 ^ (prefixWord ++ tailWord_3190575).sum := by decide
  have hdescent : baseEnd_3190575 < baseStart_3190575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190579 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 2, 4]
def baseStart_3190579 : Nat := 118140960795 + 3190579 * 2 ^ 59
def prefixEnd_3190579 : Nat := 4983230072969 + 3 ^ 40 * 3190579 * 2
def baseEnd_3190579 : Nat := 1092200395427718385792867

theorem tailTrace_3190579 : CollatzResearch.WordTrace tailWord_3190579 prefixEnd_3190579 1092200395427718385792867 := by
  unfold tailWord_3190579
  simp only [CollatzResearch.WordTrace]
  refine ⟨116369976308084665356006791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77579984205389776904004527 116369976308084665356006791)
  ·
    refine ⟨174554964462126998034010187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116369976308084665356006791 174554964462126998034010187)
    ·
      refine ⟨261832446693190497051015281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174554964462126998034010187 261832446693190497051015281)
      ·
        refine ⟨196374335019892872788261461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261832446693190497051015281 196374335019892872788261461)
        ·
          refine ⟨2301261738514369602987439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 196374335019892872788261461 2301261738514369602987439)
          ·
            refine ⟨3451892607771554404481159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301261738514369602987439 3451892607771554404481159)
            ·
              refine ⟨5177838911657331606721739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451892607771554404481159 5177838911657331606721739)
              ·
                refine ⟨7766758367485997410082609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5177838911657331606721739 7766758367485997410082609)
                ·
                  refine ⟨5825068775614498057561957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7766758367485997410082609 5825068775614498057561957)
                  ·
                    refine ⟨1092200395427718385792867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5825068775614498057561957 1092200395427718385792867)
                    ·
                      rfl

theorem cell22_3190579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 2, 4].length) (baseStart_3190579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190579 prefixEnd_3190579 := by exact prefixLift 3190579
  have htrace : WordTrace (prefixWord ++ tailWord_3190579) baseStart_3190579 baseEnd_3190579 := by
    simpa [prefixWord, tailWord_3190579, baseEnd_3190579] using wordTrace_append hprefix tailTrace_3190579
  have hstable : (prefixWord ++ tailWord_3190579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190579).length < 2 ^ (prefixWord ++ tailWord_3190579).sum := by decide
  have hdescent : baseEnd_3190579 < baseStart_3190579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190598 : List Nat := [6, 1, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_3190598 : Nat := 118140960795 + 3190598 * 2 ^ 59
def prefixEnd_3190598 : Nat := 4983230072969 + 3 ^ 40 * 3190598 * 2
def baseEnd_3190598 : Nat := 1092206899516008669567809

theorem tailTrace_3190598 : CollatzResearch.WordTrace tailWord_3190598 prefixEnd_3190598 1092206899516008669567809 := by
  unfold tailWord_3190598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3636583415469244737529639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77580446196677221067298965 3636583415469244737529639)
  ·
    refine ⟨5454875123203867106294459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3636583415469244737529639 5454875123203867106294459)
    ·
      refine ⟨8182312684805800659441689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5454875123203867106294459 8182312684805800659441689)
      ·
        refine ⟨6136734513604350494581267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8182312684805800659441689 6136734513604350494581267)
        ·
          refine ⟨9205101770406525741871901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6136734513604350494581267 9205101770406525741871901)
          ·
            refine ⟨3451913163902447153201963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9205101770406525741871901 3451913163902447153201963)
            ·
              refine ⟨5177869745853670729802945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451913163902447153201963 5177869745853670729802945)
              ·
                refine ⟨3883402309390253047352209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5177869745853670729802945 3883402309390253047352209)
                ·
                  refine ⟨2912551732042689785514157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3883402309390253047352209 2912551732042689785514157)
                  ·
                    refine ⟨1092206899516008669567809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2912551732042689785514157 1092206899516008669567809)
                    ·
                      rfl

theorem cell22_3190598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_3190598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190598 prefixEnd_3190598 := by exact prefixLift 3190598
  have htrace : WordTrace (prefixWord ++ tailWord_3190598) baseStart_3190598 baseEnd_3190598 := by
    simpa [prefixWord, tailWord_3190598, baseEnd_3190598] using wordTrace_append hprefix tailTrace_3190598
  have hstable : (prefixWord ++ tailWord_3190598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190598).length < 2 ^ (prefixWord ++ tailWord_3190598).sum := by decide
  have hdescent : baseEnd_3190598 < baseStart_3190598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190609 : List Nat := [1, 2, 2, 1, 5, 1, 2, 4, 1, 3]
def baseStart_3190609 : Nat := 118140960795 + 3190609 * 2 ^ 59
def prefixEnd_3190609 : Nat := 4983230072969 + 3 ^ 40 * 3190609 * 2
def baseEnd_3190609 : Nat := 1092210665040808307542775

theorem tailTrace_3190609 : CollatzResearch.WordTrace tailWord_3190609 prefixEnd_3190609 1092210665040808307542775 := by
  unfold tailWord_3190609
  simp only [CollatzResearch.WordTrace]
  refine ⟨116371070497975980479598881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77580713665317320319732587 116371070497975980479598881)
  ·
    refine ⟨87278302873481985359699161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116371070497975980479598881 87278302873481985359699161)
    ·
      refine ⟨65458727155111489019774371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87278302873481985359699161 65458727155111489019774371)
      ·
        refine ⟨98188090732667233529661557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65458727155111489019774371 98188090732667233529661557)
        ·
          refine ⟨9205133506187553143405771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98188090732667233529661557 9205133506187553143405771)
          ·
            refine ⟨13807700259281329715108657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9205133506187553143405771 13807700259281329715108657)
            ·
              refine ⟨10355775194460997286331493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13807700259281329715108657 10355775194460997286331493)
              ·
                refine ⟨1941707848961436991187155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10355775194460997286331493 1941707848961436991187155)
                ·
                  refine ⟨2912561773442155486780733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941707848961436991187155 2912561773442155486780733)
                  ·
                    refine ⟨1092210665040808307542775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2912561773442155486780733 1092210665040808307542775)
                    ·
                      rfl

theorem cell22_3190609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_3190609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190609 prefixEnd_3190609 := by exact prefixLift 3190609
  have htrace : WordTrace (prefixWord ++ tailWord_3190609) baseStart_3190609 baseEnd_3190609 := by
    simpa [prefixWord, tailWord_3190609, baseEnd_3190609] using wordTrace_append hprefix tailTrace_3190609
  have hstable : (prefixWord ++ tailWord_3190609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190609).length < 2 ^ (prefixWord ++ tailWord_3190609).sum := by decide
  have hdescent : baseEnd_3190609 < baseStart_3190609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190686 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_3190686 : Nat := 118140960795 + 3190686 * 2 ^ 59
def prefixEnd_3190686 : Nat := 4983230072969 + 3 ^ 40 * 3190686 * 2
def baseEnd_3190686 : Nat := 1092237023714405773367539

theorem tailTrace_3190686 : CollatzResearch.WordTrace tailWord_3190686 prefixEnd_3190686 1092237023714405773367539 := by
  unfold tailWord_3190686
  simp only [CollatzResearch.WordTrace]
  refine ⟨14546734864837127828768989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77582585945798015086767941 14546734864837127828768989)
  ·
    refine ⟨5455025574313922935788371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14546734864837127828768989 5455025574313922935788371)
    ·
      refine ⟨8182538361470884403682557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5455025574313922935788371 8182538361470884403682557)
      ·
        refine ⟨3068451885551581651380959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8182538361470884403682557 3068451885551581651380959)
        ·
          refine ⟨4602677828327372477071439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3068451885551581651380959 4602677828327372477071439)
          ·
            refine ⟨6904016742491058715607159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4602677828327372477071439 6904016742491058715607159)
            ·
              refine ⟨10356025113736588073410739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6904016742491058715607159 10356025113736588073410739)
              ·
                refine ⟨15534037670604882110116109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10356025113736588073410739 15534037670604882110116109)
                ·
                  refine ⟨5825264126476830791293541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15534037670604882110116109 5825264126476830791293541)
                  ·
                    refine ⟨1092237023714405773367539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5825264126476830791293541 1092237023714405773367539)
                    ·
                      rfl

theorem cell22_3190686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_3190686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190686 prefixEnd_3190686 := by exact prefixLift 3190686
  have htrace : WordTrace (prefixWord ++ tailWord_3190686) baseStart_3190686 baseEnd_3190686 := by
    simpa [prefixWord, tailWord_3190686, baseEnd_3190686] using wordTrace_append hprefix tailTrace_3190686
  have hstable : (prefixWord ++ tailWord_3190686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190686).length < 2 ^ (prefixWord ++ tailWord_3190686).sum := by decide
  have hdescent : baseEnd_3190686 < baseStart_3190686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190727 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 3, 3]
def baseStart_3190727 : Nat := 118140960795 + 3190727 * 2 ^ 59
def prefixEnd_3190727 : Nat := 4983230072969 + 3 ^ 40 * 3190727 * 2
def baseEnd_3190727 : Nat := 1092251058852295333092413

theorem tailTrace_3190727 : CollatzResearch.WordTrace tailWord_3190727 prefixEnd_3190727 1092251058852295333092413 := by
  unfold tailWord_3190727
  simp only [CollatzResearch.WordTrace]
  refine ⟨116375374311548486632394435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77583582874365657754929623 116375374311548486632394435)
  ·
    refine ⟨174563061467322729948591653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116375374311548486632394435 174563061467322729948591653)
    ·
      refine ⟨32730574025123011865360935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174563061467322729948591653 32730574025123011865360935)
      ·
        refine ⟨49095861037684517798041403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32730574025123011865360935 49095861037684517798041403)
        ·
          refine ⟨73643791556526776697062105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49095861037684517798041403 73643791556526776697062105)
          ·
            refine ⟨55232843667395082522796579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73643791556526776697062105 55232843667395082522796579)
            ·
              refine ⟨82849265501092623784194869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55232843667395082522796579 82849265501092623784194869)
              ·
                refine ⟨7767118640727433479768269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82849265501092623784194869 7767118640727433479768269)
                ·
                  refine ⟨2912669490272787554913101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7767118640727433479768269 2912669490272787554913101)
                  ·
                    refine ⟨1092251058852295333092413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2912669490272787554913101 1092251058852295333092413)
                    ·
                      rfl

theorem cell22_3190727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_3190727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190727 prefixEnd_3190727 := by exact prefixLift 3190727
  have htrace : WordTrace (prefixWord ++ tailWord_3190727) baseStart_3190727 baseEnd_3190727 := by
    simpa [prefixWord, tailWord_3190727, baseEnd_3190727] using wordTrace_append hprefix tailTrace_3190727
  have hstable : (prefixWord ++ tailWord_3190727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190727).length < 2 ^ (prefixWord ++ tailWord_3190727).sum := by decide
  have hdescent : baseEnd_3190727 < baseStart_3190727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190774 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_3190774 : Nat := 118140960795 + 3190774 * 2 ^ 59
def prefixEnd_3190774 : Nat := 4983230072969 + 3 ^ 40 * 3190774 * 2
def baseEnd_3190774 : Nat := 364089049304267625722423

theorem tailTrace_3190774 : CollatzResearch.WordTrace tailWord_3190774 prefixEnd_3190774 364089049304267625722423 := by
  unfold tailWord_3190774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7273568033898638353709711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77584725694918809106236917 7273568033898638353709711)
  ·
    refine ⟨10910352050847957530564567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7273568033898638353709711 10910352050847957530564567)
    ·
      refine ⟨16365528076271936295846851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10910352050847957530564567 16365528076271936295846851)
      ·
        refine ⟨24548292114407904443770277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16365528076271936295846851 24548292114407904443770277)
        ·
          refine ⟨4602804771451482083206927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24548292114407904443770277 4602804771451482083206927)
          ·
            refine ⟨6904207157177223124810391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4602804771451482083206927 6904207157177223124810391)
            ·
              refine ⟨10356310735765834687215587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6904207157177223124810391 10356310735765834687215587)
              ·
                refine ⟨15534466103648752030823381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10356310735765834687215587 15534466103648752030823381)
                ·
                  refine ⟨364089049304267625722423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15534466103648752030823381 364089049304267625722423)
                  ·
                    rfl

theorem cell22_3190774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_3190774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190774 prefixEnd_3190774 := by exact prefixLift 3190774
  have htrace : WordTrace (prefixWord ++ tailWord_3190774) baseStart_3190774 baseEnd_3190774 := by
    simpa [prefixWord, tailWord_3190774, baseEnd_3190774] using wordTrace_append hprefix tailTrace_3190774
  have hstable : (prefixWord ++ tailWord_3190774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190774).length < 2 ^ (prefixWord ++ tailWord_3190774).sum := by decide
  have hdescent : baseEnd_3190774 < baseStart_3190774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190832 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 4, 4]
def baseStart_3190832 : Nat := 118140960795 + 3190832 * 2 ^ 59
def prefixEnd_3190832 : Nat := 4983230072969 + 3 ^ 40 * 3190832 * 2
def baseEnd_3190832 : Nat := 1092287002498110059217091

theorem tailTrace_3190832 : CollatzResearch.WordTrace tailWord_3190832 prefixEnd_3190832 1092287002498110059217091 := by
  unfold tailWord_3190832
  simp only [CollatzResearch.WordTrace]
  refine ⟨58189601988084044782483375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77586135984112059709977833 58189601988084044782483375)
  ·
    refine ⟨87284402982126067173725063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58189601988084044782483375 87284402982126067173725063)
    ·
      refine ⟨130926604473189100760587595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87284402982126067173725063 130926604473189100760587595)
      ·
        refine ⟨196389906709783651140881393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130926604473189100760587595 196389906709783651140881393)
        ·
          refine ⟨147292430032337738355661045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196389906709783651140881393 147292430032337738355661045)
          ·
            refine ⟨13808665315531662970843223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147292430032337738355661045 13808665315531662970843223)
            ·
              refine ⟨20712997973297494456264835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13808665315531662970843223 20712997973297494456264835)
              ·
                refine ⟨31069496959946241684397253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20712997973297494456264835 31069496959946241684397253)
                ·
                  refine ⟨5825530679989920315824485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31069496959946241684397253 5825530679989920315824485)
                  ·
                    refine ⟨1092287002498110059217091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5825530679989920315824485 1092287002498110059217091)
                    ·
                      rfl

theorem cell22_3190832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_3190832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190832 prefixEnd_3190832 := by exact prefixLift 3190832
  have htrace : WordTrace (prefixWord ++ tailWord_3190832) baseStart_3190832 baseEnd_3190832 := by
    simpa [prefixWord, tailWord_3190832, baseEnd_3190832] using wordTrace_append hprefix tailTrace_3190832
  have hstable : (prefixWord ++ tailWord_3190832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190832).length < 2 ^ (prefixWord ++ tailWord_3190832).sum := by decide
  have hdescent : baseEnd_3190832 < baseStart_3190832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190834 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_3190834 : Nat := 118140960795 + 3190834 * 2 ^ 59
def prefixEnd_3190834 : Nat := 4983230072969 + 3 ^ 40 * 3190834 * 2
def baseEnd_3190834 : Nat := 1092287687138982720667085

theorem tailTrace_3190834 : CollatzResearch.WordTrace tailWord_3190834 prefixEnd_3190834 1092287687138982720667085 := by
  unfold tailWord_3190834
  simp only [CollatzResearch.WordTrace]
  refine ⟨29094819230540210976634889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77586184614773895937693037 29094819230540210976634889)
  ·
    refine ⟨21821114422905158232476167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29094819230540210976634889 21821114422905158232476167)
    ·
      refine ⟨32731671634357737348714251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21821114422905158232476167 32731671634357737348714251)
      ·
        refine ⟨49097507451536606023071377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32731671634357737348714251 49097507451536606023071377)
        ·
          refine ⟨36823130588652454517303533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49097507451536606023071377 36823130588652454517303533)
          ·
            refine ⟨13808673970744670443988825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36823130588652454517303533 13808673970744670443988825)
            ·
              refine ⟨10356505478058502832991619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13808673970744670443988825 10356505478058502832991619)
              ·
                refine ⟨15534758217087754249487429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10356505478058502832991619 15534758217087754249487429)
                ·
                  refine ⟨2912767165703953921778893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15534758217087754249487429 2912767165703953921778893)
                  ·
                    refine ⟨1092287687138982720667085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2912767165703953921778893 1092287687138982720667085)
                    ·
                      rfl

theorem cell22_3190834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_3190834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190834 prefixEnd_3190834 := by exact prefixLift 3190834
  have htrace : WordTrace (prefixWord ++ tailWord_3190834) baseStart_3190834 baseEnd_3190834 := by
    simpa [prefixWord, tailWord_3190834, baseEnd_3190834] using wordTrace_append hprefix tailTrace_3190834
  have hstable : (prefixWord ++ tailWord_3190834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190834).length < 2 ^ (prefixWord ++ tailWord_3190834).sum := by decide
  have hdescent : baseEnd_3190834 < baseStart_3190834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190866 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_3190866 : Nat := 118140960795 + 3190866 * 2 ^ 59
def prefixEnd_3190866 : Nat := 4983230072969 + 3 ^ 40 * 3190866 * 2
def baseEnd_3190866 : Nat := 1092298641392945303866987

theorem tailTrace_3190866 : CollatzResearch.WordTrace tailWord_3190866 prefixEnd_3190866 1092298641392945303866987 := by
  unfold tailWord_3190866
  simp only [CollatzResearch.WordTrace]
  refine ⟨29095111014511228342926113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77586962705363275581136301 29095111014511228342926113)
  ·
    refine ⟨21821333260883421257194585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29095111014511228342926113 21821333260883421257194585)
    ·
      refine ⟨16365999945662565942895939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21821333260883421257194585 16365999945662565942895939)
      ·
        refine ⟨24548999918493848914343909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16365999945662565942895939 24548999918493848914343909)
        ·
          refine ⟨4602937484717596671439483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24548999918493848914343909 4602937484717596671439483)
          ·
            refine ⟨6904406227076395007159225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4602937484717596671439483 6904406227076395007159225)
            ·
              refine ⟨5178304670307296255369419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6904406227076395007159225 5178304670307296255369419)
              ·
                refine ⟨7767457005460944383054129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5178304670307296255369419 7767457005460944383054129)
                ·
                  refine ⟨5825592754095708287290597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7767457005460944383054129 5825592754095708287290597)
                  ·
                    refine ⟨1092298641392945303866987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5825592754095708287290597 1092298641392945303866987)
                    ·
                      rfl

theorem cell22_3190866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_3190866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190866 prefixEnd_3190866 := by exact prefixLift 3190866
  have htrace : WordTrace (prefixWord ++ tailWord_3190866) baseStart_3190866 baseEnd_3190866 := by
    simpa [prefixWord, tailWord_3190866, baseEnd_3190866] using wordTrace_append hprefix tailTrace_3190866
  have hstable : (prefixWord ++ tailWord_3190866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190866).length < 2 ^ (prefixWord ++ tailWord_3190866).sum := by decide
  have hdescent : baseEnd_3190866 < baseStart_3190866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190909 : List Nat := [1, 4, 1, 1, 3, 2, 2, 3, 5]
def baseStart_3190909 : Nat := 118140960795 + 3190909 * 2 ^ 59
def prefixEnd_3190909 : Nat := 4983230072969 + 3 ^ 40 * 3190909 * 2
def baseEnd_3190909 : Nat := 364104453723902508347285

theorem tailTrace_3190909 : CollatzResearch.WordTrace tailWord_3190909 prefixEnd_3190909 364104453723902508347285 := by
  unfold tailWord_3190909
  simp only [CollatzResearch.WordTrace]
  refine ⟨116382012396889131715519781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77588008264592754477013187 116382012396889131715519781)
  ·
    refine ⟨21821627324416712196659959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116382012396889131715519781 21821627324416712196659959)
    ·
      refine ⟨32732440986625068294989939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21821627324416712196659959 32732440986625068294989939)
      ·
        refine ⟨49098661479937602442484909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32732440986625068294989939 49098661479937602442484909)
        ·
          refine ⟨18411998054976600915931841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49098661479937602442484909 18411998054976600915931841)
          ·
            refine ⟨13808998541232450686948881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18411998054976600915931841 13808998541232450686948881)
            ·
              refine ⟨10356748905924338015211661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13808998541232450686948881 10356748905924338015211661)
              ·
                refine ⟨3883780839721626755704373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10356748905924338015211661 3883780839721626755704373)
                ·
                  refine ⟨364104453723902508347285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3883780839721626755704373 364104453723902508347285)
                  ·
                    rfl

theorem cell22_3190909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_3190909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190909 prefixEnd_3190909 := by exact prefixLift 3190909
  have htrace : WordTrace (prefixWord ++ tailWord_3190909) baseStart_3190909 baseEnd_3190909 := by
    simpa [prefixWord, tailWord_3190909, baseEnd_3190909] using wordTrace_append hprefix tailTrace_3190909
  have hstable : (prefixWord ++ tailWord_3190909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190909).length < 2 ^ (prefixWord ++ tailWord_3190909).sum := by decide
  have hdescent : baseEnd_3190909 < baseStart_3190909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190984 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 2, 4]
def baseStart_3190984 : Nat := 118140960795 + 3190984 * 2 ^ 59
def prefixEnd_3190984 : Nat := 4983230072969 + 3 ^ 40 * 3190984 * 2
def baseEnd_3190984 : Nat := 1092339035204432329416625

theorem tailTrace_3190984 : CollatzResearch.WordTrace tailWord_3190984 prefixEnd_3190984 1092339035204432329416625 := by
  unfold tailWord_3190984
  simp only [CollatzResearch.WordTrace]
  refine ⟨58192373935808709762250003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77589831914411613016333337 58192373935808709762250003)
  ·
    refine ⟨87288560903713064643375005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58192373935808709762250003 87288560903713064643375005)
    ·
      refine ⟨32733210338892399241265627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87288560903713064643375005 32733210338892399241265627)
      ·
        refine ⟨49099815508338598861898441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32733210338892399241265627 49099815508338598861898441)
        ·
          refine ⟨36824861631253949146423831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49099815508338598861898441 36824861631253949146423831)
          ·
            refine ⟨55237292446880923719635747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36824861631253949146423831 55237292446880923719635747)
            ·
              refine ⟨82855938670321385579453621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55237292446880923719635747 82855938670321385579453621)
              ·
                refine ⟨7767744250342629898073777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82855938670321385579453621 7767744250342629898073777)
                ·
                  refine ⟨5825808187756972423555333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7767744250342629898073777 5825808187756972423555333)
                  ·
                    refine ⟨1092339035204432329416625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5825808187756972423555333 1092339035204432329416625)
                    ·
                      rfl

theorem cell22_3190984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_3190984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3190984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3190984 prefixEnd_3190984 := by exact prefixLift 3190984
  have htrace : WordTrace (prefixWord ++ tailWord_3190984) baseStart_3190984 baseEnd_3190984 := by
    simpa [prefixWord, tailWord_3190984, baseEnd_3190984] using wordTrace_append hprefix tailTrace_3190984
  have hstable : (prefixWord ++ tailWord_3190984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190984).length < 2 ^ (prefixWord ++ tailWord_3190984).sum := by decide
  have hdescent : baseEnd_3190984 < baseStart_3190984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191005 : List Nat := [1, 4, 3, 2, 1, 2, 3, 2, 4]
def baseStart_3191005 : Nat := 118140960795 + 3191005 * 2 ^ 59
def prefixEnd_3191005 : Nat := 4983230072969 + 3 ^ 40 * 3191005 * 2
def baseEnd_3191005 : Nat := 364115407977865091547187

theorem tailTrace_3191005 : CollatzResearch.WordTrace tailWord_3191005 prefixEnd_3191005 364115407977865091547187 := by
  unfold tailWord_3191005
  simp only [CollatzResearch.WordTrace]
  refine ⟨116385513804541340111014469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77590342536360893407342979 116385513804541340111014469)
  ·
    refine ⟨21822283838351501270815213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116385513804541340111014469 21822283838351501270815213)
    ·
      refine ⟨8183356439381812976555705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21822283838351501270815213 8183356439381812976555705)
      ·
        refine ⟨6137517329536359732416779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8183356439381812976555705 6137517329536359732416779)
        ·
          refine ⟨9206275994304539598625169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6137517329536359732416779 9206275994304539598625169)
          ·
            refine ⟨6904706995728404698968877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9206275994304539598625169 6904706995728404698968877)
            ·
              refine ⟨2589265123398151762113329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6904706995728404698968877 2589265123398151762113329)
              ·
                refine ⟨1941948842548613821584997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2589265123398151762113329 1941948842548613821584997)
                ·
                  refine ⟨364115407977865091547187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1941948842548613821584997 364115407977865091547187)
                  ·
                    rfl

theorem cell22_3191005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_3191005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191005 prefixEnd_3191005 := by exact prefixLift 3191005
  have htrace : WordTrace (prefixWord ++ tailWord_3191005) baseStart_3191005 baseEnd_3191005 := by
    simpa [prefixWord, tailWord_3191005, baseEnd_3191005] using wordTrace_append hprefix tailTrace_3191005
  have hstable : (prefixWord ++ tailWord_3191005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191005).length < 2 ^ (prefixWord ++ tailWord_3191005).sum := by decide
  have hdescent : baseEnd_3191005 < baseStart_3191005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191076 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_3191076 : Nat := 118140960795 + 3191076 * 2 ^ 59
def prefixEnd_3191076 : Nat := 4983230072969 + 3 ^ 40 * 3191076 * 2
def baseEnd_3191076 : Nat := 1092370528684574756116343

theorem tailTrace_3191076 : CollatzResearch.WordTrace tailWord_3191076 prefixEnd_3191076 1092370528684574756116343 := by
  unfold tailWord_3191076
  simp only [CollatzResearch.WordTrace]
  refine ⟨58194051693642059618424541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77592068924856079491232721 58194051693642059618424541)
  ·
    refine ⟨21822769385115772356909203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58194051693642059618424541 21822769385115772356909203)
    ·
      refine ⟨32734154077673658535363805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21822769385115772356909203 32734154077673658535363805)
      ·
        refine ⟨12275307779127621950761427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32734154077673658535363805 12275307779127621950761427)
        ·
          refine ⟨18412961668691432926142141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12275307779127621950761427 18412961668691432926142141)
          ·
            refine ⟨6904860625759287347303303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18412961668691432926142141 6904860625759287347303303)
            ·
              refine ⟨10357290938638931020954955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6904860625759287347303303 10357290938638931020954955)
              ·
                refine ⟨15535936407958396531432433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10357290938638931020954955 15535936407958396531432433)
                ·
                  refine ⟨11651952305968797398574325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15535936407958396531432433 11651952305968797398574325)
                  ·
                    refine ⟨1092370528684574756116343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11651952305968797398574325 1092370528684574756116343)
                    ·
                      rfl

theorem cell22_3191076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_3191076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191076 prefixEnd_3191076 := by exact prefixLift 3191076
  have htrace : WordTrace (prefixWord ++ tailWord_3191076) baseStart_3191076 baseEnd_3191076 := by
    simpa [prefixWord, tailWord_3191076, baseEnd_3191076] using wordTrace_append hprefix tailTrace_3191076
  have hstable : (prefixWord ++ tailWord_3191076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191076).length < 2 ^ (prefixWord ++ tailWord_3191076).sum := by decide
  have hdescent : baseEnd_3191076 < baseStart_3191076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191091 : List Nat := [1, 1, 1, 2, 5, 1, 2, 4, 1, 4]
def baseStart_3191091 : Nat := 118140960795 + 3191091 * 2 ^ 59
def prefixEnd_3191091 : Nat := 4983230072969 + 3 ^ 40 * 3191091 * 2
def baseEnd_3191091 : Nat := 1092375663491119716991297

theorem tailTrace_3191091 : CollatzResearch.WordTrace tailWord_3191091 prefixEnd_3191091 1092375663491119716991297 := by
  unfold tailWord_3191091
  simp only [CollatzResearch.WordTrace]
  refine ⟨116388650482229776798645127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77592433654819851199096751 116388650482229776798645127)
  ·
    refine ⟨174582975723344665197967691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116388650482229776798645127 174582975723344665197967691)
    ·
      refine ⟨261874463585016997796951537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174582975723344665197967691 261874463585016997796951537)
      ·
        refine ⟨196405847688762748347713653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261874463585016997796951537 196405847688762748347713653)
        ·
          refine ⟨18413048220821507657598155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196405847688762748347713653 18413048220821507657598155)
          ·
            refine ⟨27619572331232261486397233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18413048220821507657598155 27619572331232261486397233)
            ·
              refine ⟨20714679248424196114797925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27619572331232261486397233 20714679248424196114797925)
              ·
                refine ⟨3884002359079536771524611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20714679248424196114797925 3884002359079536771524611)
                ·
                  refine ⟨5826003538619305157286917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3884002359079536771524611 5826003538619305157286917)
                  ·
                    refine ⟨1092375663491119716991297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5826003538619305157286917 1092375663491119716991297)
                    ·
                      rfl

theorem cell22_3191091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 4].length) (baseStart_3191091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191091 prefixEnd_3191091 := by exact prefixLift 3191091
  have htrace : WordTrace (prefixWord ++ tailWord_3191091) baseStart_3191091 baseEnd_3191091 := by
    simpa [prefixWord, tailWord_3191091, baseEnd_3191091] using wordTrace_append hprefix tailTrace_3191091
  have hstable : (prefixWord ++ tailWord_3191091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191091).length < 2 ^ (prefixWord ++ tailWord_3191091).sum := by decide
  have hdescent : baseEnd_3191091 < baseStart_3191091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191104 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 3, 5]
def baseStart_3191104 : Nat := 118140960795 + 3191104 * 2 ^ 59
def prefixEnd_3191104 : Nat := 4983230072969 + 3 ^ 40 * 3191104 * 2
def baseEnd_3191104 : Nat := 1092380113656792016416257

theorem tailTrace_3191104 : CollatzResearch.WordTrace tailWord_3191104 prefixEnd_3191104 1092380113656792016416257 := by
  unfold tailWord_3191104
  simp only [CollatzResearch.WordTrace]
  refine ⟨58194562315591340009434183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77592749754121786679245577 58194562315591340009434183)
  ·
    refine ⟨87291843473387010014151275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58194562315591340009434183 87291843473387010014151275)
    ·
      refine ⟨130937765210080515021226913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87291843473387010014151275 130937765210080515021226913)
      ·
        refine ⟨98203323907560386265920185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130937765210080515021226913 98203323907560386265920185)
        ·
          refine ⟨73652492930670289699440139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98203323907560386265920185 73652492930670289699440139)
          ·
            refine ⟨110478739396005434549160209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73652492930670289699440139 110478739396005434549160209)
            ·
              refine ⟨82859054547004075911870157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110478739396005434549160209 82859054547004075911870157)
              ·
                refine ⟨31072145455126528466951309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82859054547004075911870157 31072145455126528466951309)
                ·
                  refine ⟨11652054545672448175106741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31072145455126528466951309 11652054545672448175106741)
                  ·
                    refine ⟨1092380113656792016416257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11652054545672448175106741 1092380113656792016416257)
                    ·
                      rfl

theorem cell22_3191104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_3191104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191104 prefixEnd_3191104 := by exact prefixLift 3191104
  have htrace : WordTrace (prefixWord ++ tailWord_3191104) baseStart_3191104 baseEnd_3191104 := by
    simpa [prefixWord, tailWord_3191104, baseEnd_3191104] using wordTrace_append hprefix tailTrace_3191104
  have hstable : (prefixWord ++ tailWord_3191104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191104).length < 2 ^ (prefixWord ++ tailWord_3191104).sum := by decide
  have hdescent : baseEnd_3191104 < baseStart_3191104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191138 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3191138 : Nat := 118140960795 + 3191138 * 2 ^ 59
def prefixEnd_3191138 : Nat := 4983230072969 + 3 ^ 40 * 3191138 * 2
def baseEnd_3191138 : Nat := 1092391752551627261066153

theorem tailTrace_3191138 : CollatzResearch.WordTrace tailWord_3191138 prefixEnd_3191138 1092391752551627261066153 := by
  unfold tailWord_3191138
  simp only [CollatzResearch.WordTrace]
  refine ⟨29097591178264875956401517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77593576475373002550404045 29097591178264875956401517)
  ·
    refine ⟨10911596691849328483650569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29097591178264875956401517 10911596691849328483650569)
    ·
      refine ⟨8183697518886996362737927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10911596691849328483650569 8183697518886996362737927)
      ·
        refine ⟨12275546278330494544106891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8183697518886996362737927 12275546278330494544106891)
        ·
          refine ⟨18413319417495741816160337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12275546278330494544106891 18413319417495741816160337)
          ·
            refine ⟨13809989563121806362120253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18413319417495741816160337 13809989563121806362120253)
            ·
              refine ⟨5178746086170677385795095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13809989563121806362120253 5178746086170677385795095)
              ·
                refine ⟨7768119129256016078692643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5178746086170677385795095 7768119129256016078692643)
                ·
                  refine ⟨11652178693884024118038965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7768119129256016078692643 11652178693884024118038965)
                  ·
                    refine ⟨1092391752551627261066153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11652178693884024118038965 1092391752551627261066153)
                    ·
                      rfl

theorem cell22_3191138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3191138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191138 prefixEnd_3191138 := by exact prefixLift 3191138
  have htrace : WordTrace (prefixWord ++ tailWord_3191138) baseStart_3191138 baseEnd_3191138 := by
    simpa [prefixWord, tailWord_3191138, baseEnd_3191138] using wordTrace_append hprefix tailTrace_3191138
  have hstable : (prefixWord ++ tailWord_3191138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191138).length < 2 ^ (prefixWord ++ tailWord_3191138).sum := by decide
  have hdescent : baseEnd_3191138 < baseStart_3191138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191277 : List Nat := [1, 5, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_3191277 : Nat := 118140960795 + 3191277 * 2 ^ 59
def prefixEnd_3191277 : Nat := 4983230072969 + 3 ^ 40 * 3191277 * 2
def baseEnd_3191277 : Nat := 1092439335092277231840727

theorem tailTrace_3191277 : CollatzResearch.WordTrace tailWord_3191277 prefixEnd_3191277 1092439335092277231840727 := by
  unfold tailWord_3191277
  simp only [CollatzResearch.WordTrace]
  refine ⟨116395434459555930564916085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77596956306370620376610723 116395434459555930564916085)
  ·
    refine ⟨10912071980583368490460883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116395434459555930564916085 10912071980583368490460883)
    ·
      refine ⟨16368107970875052735691325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10912071980583368490460883 16368107970875052735691325)
      ·
        refine ⟨6138040489078144775884247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16368107970875052735691325 6138040489078144775884247)
        ·
          refine ⟨9207060733617217163826371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6138040489078144775884247 9207060733617217163826371)
          ·
            refine ⟨13810591100425825745739557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9207060733617217163826371 13810591100425825745739557)
            ·
              refine ⟨2589485831329842327326167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13810591100425825745739557 2589485831329842327326167)
              ·
                refine ⟨3884228746994763490989251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589485831329842327326167 3884228746994763490989251)
                ·
                  refine ⟨5826343120492145236483877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3884228746994763490989251 5826343120492145236483877)
                  ·
                    refine ⟨1092439335092277231840727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5826343120492145236483877 1092439335092277231840727)
                    ·
                      rfl

theorem cell22_3191277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_3191277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191277 prefixEnd_3191277 := by exact prefixLift 3191277
  have htrace : WordTrace (prefixWord ++ tailWord_3191277) baseStart_3191277 baseEnd_3191277 := by
    simpa [prefixWord, tailWord_3191277, baseEnd_3191277] using wordTrace_append hprefix tailTrace_3191277
  have hstable : (prefixWord ++ tailWord_3191277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191277).length < 2 ^ (prefixWord ++ tailWord_3191277).sum := by decide
  have hdescent : baseEnd_3191277 < baseStart_3191277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191307 : List Nat := [1, 1, 1, 1, 7, 2, 3, 1, 2, 3]
def baseStart_3191307 : Nat := 118140960795 + 3191307 * 2 ^ 59
def prefixEnd_3191307 : Nat := 4983230072969 + 3 ^ 40 * 3191307 * 2
def baseEnd_3191307 : Nat := 1092449604705367153590635

theorem tailTrace_3191307 : CollatzResearch.WordTrace tailWord_3191307 prefixEnd_3191307 1092449604705367153590635 := by
  unfold tailWord_3191307
  simp only [CollatzResearch.WordTrace]
  refine ⟨116396528649447245688508175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77597685766298163792338783 116396528649447245688508175)
  ·
    refine ⟨174594792974170868532762263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116396528649447245688508175 174594792974170868532762263)
    ·
      refine ⟨261892189461256302799143395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174594792974170868532762263 261892189461256302799143395)
      ·
        refine ⟨392838284191884454198715093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261892189461256302799143395 392838284191884454198715093)
        ·
          refine ⟨9207147285747291895282385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 392838284191884454198715093 9207147285747291895282385)
          ·
            refine ⟨6905360464310468921461789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9207147285747291895282385 6905360464310468921461789)
            ·
              refine ⟨2589510174116425845548171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6905360464310468921461789 2589510174116425845548171)
              ·
                refine ⟨3884265261174638768322257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589510174116425845548171 3884265261174638768322257)
                ·
                  refine ⟨2913198945880979076241693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3884265261174638768322257 2913198945880979076241693)
                  ·
                    refine ⟨1092449604705367153590635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2913198945880979076241693 1092449604705367153590635)
                    ·
                      rfl

theorem cell22_3191307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 2, 3].length) (baseStart_3191307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191307 prefixEnd_3191307 := by exact prefixLift 3191307
  have htrace : WordTrace (prefixWord ++ tailWord_3191307) baseStart_3191307 baseEnd_3191307 := by
    simpa [prefixWord, tailWord_3191307, baseEnd_3191307] using wordTrace_append hprefix tailTrace_3191307
  have hstable : (prefixWord ++ tailWord_3191307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191307).length < 2 ^ (prefixWord ++ tailWord_3191307).sum := by decide
  have hdescent : baseEnd_3191307 < baseStart_3191307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191320 : List Nat := [2, 1, 2, 3, 3, 3, 2, 6]
def baseStart_3191320 : Nat := 118140960795 + 3191320 * 2 ^ 59
def prefixEnd_3191320 : Nat := 4983230072969 + 3 ^ 40 * 3191320 * 2
def baseEnd_3191320 : Nat := 121383783874559939223955

theorem tailTrace_3191320 : CollatzResearch.WordTrace tailWord_3191320 prefixEnd_3191320 121383783874559939223955 := by
  unfold tailWord_3191320
  simp only [CollatzResearch.WordTrace]
  refine ⟨58198501399200074454365707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77598001865600099272487609 58198501399200074454365707)
  ·
    refine ⟨87297752098800111681548561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58198501399200074454365707 87297752098800111681548561)
    ·
      refine ⟨65473314074100083761161421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87297752098800111681548561 65473314074100083761161421)
      ·
        refine ⟨24552492777787531410435533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65473314074100083761161421 24552492777787531410435533)
        ·
          refine ⟨9207184791670324278913325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24552492777787531410435533 9207184791670324278913325)
          ·
            refine ⟨3452694296876371604592497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9207184791670324278913325 3452694296876371604592497)
            ·
              refine ⟨2589520722657278703444373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3452694296876371604592497 2589520722657278703444373)
              ·
                refine ⟨121383783874559939223955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2589520722657278703444373 121383783874559939223955)
                ·
                  rfl

theorem cell22_3191320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 6].length) (baseStart_3191320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191320 prefixEnd_3191320 := by exact prefixLift 3191320
  have htrace : WordTrace (prefixWord ++ tailWord_3191320) baseStart_3191320 baseEnd_3191320 := by
    simpa [prefixWord, tailWord_3191320, baseEnd_3191320] using wordTrace_append hprefix tailTrace_3191320
  have hstable : (prefixWord ++ tailWord_3191320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191320).length < 2 ^ (prefixWord ++ tailWord_3191320).sum := by decide
  have hdescent : baseEnd_3191320 < baseStart_3191320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191358 : List Nat := [4, 2, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_3191358 : Nat := 118140960795 + 3191358 * 2 ^ 59
def prefixEnd_3191358 : Nat := 4983230072969 + 3 ^ 40 * 3191358 * 2
def baseEnd_3191358 : Nat := 1092467063047620020565479

theorem tailTrace_3191358 : CollatzResearch.WordTrace tailWord_3191358 prefixEnd_3191358 1092467063047620020565479 := by
  unfold tailWord_3191358
  simp only [CollatzResearch.WordTrace]
  refine ⟨14549798596532810174826841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77598925848174987599076485 14549798596532810174826841)
  ·
    refine ⟨10912348947399607631120131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14549798596532810174826841 10912348947399607631120131)
    ·
      refine ⟨16368523421099411446680197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10912348947399607631120131 16368523421099411446680197)
      ·
        refine ⟨3069098141456139646252537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16368523421099411446680197 3069098141456139646252537)
        ·
          refine ⟨2301823606092104734689403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3069098141456139646252537 2301823606092104734689403)
          ·
            refine ⟨3452735409138157102034105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301823606092104734689403 3452735409138157102034105)
            ·
              refine ⟨2589551556853617826525579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3452735409138157102034105 2589551556853617826525579)
              ·
                refine ⟨3884327335280426739788369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589551556853617826525579 3884327335280426739788369)
                ·
                  refine ⟨2913245501460320054841277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3884327335280426739788369 2913245501460320054841277)
                  ·
                    refine ⟨1092467063047620020565479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2913245501460320054841277 1092467063047620020565479)
                    ·
                      rfl

theorem cell22_3191358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_3191358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191358 prefixEnd_3191358 := by exact prefixLift 3191358
  have htrace : WordTrace (prefixWord ++ tailWord_3191358) baseStart_3191358 baseEnd_3191358 := by
    simpa [prefixWord, tailWord_3191358, baseEnd_3191358] using wordTrace_append hprefix tailTrace_3191358
  have hstable : (prefixWord ++ tailWord_3191358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191358).length < 2 ^ (prefixWord ++ tailWord_3191358).sum := by decide
  have hdescent : baseEnd_3191358 < baseStart_3191358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191365 : List Nat := [1, 3, 1, 1, 1, 5, 4, 1, 5]
def baseStart_3191365 : Nat := 118140960795 + 3191365 * 2 ^ 59
def prefixEnd_3191365 : Nat := 4983230072969 + 3 ^ 40 * 3191365 * 2
def baseEnd_3191365 : Nat := 364156486430224778546819

theorem tailTrace_3191365 : CollatzResearch.WordTrace tailWord_3191365 prefixEnd_3191365 364156486430224778546819 := by
  unfold tailWord_3191365
  simp only [CollatzResearch.WordTrace]
  refine ⟨116398644083237121594119549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77599096055491414396079699 116398644083237121594119549)
  ·
    refine ⟨43649491531213920597794831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116398644083237121594119549 43649491531213920597794831)
    ·
      refine ⟨65474237296820880896692247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43649491531213920597794831 65474237296820880896692247)
      ·
        refine ⟨98211355945231321345038371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65474237296820880896692247 98211355945231321345038371)
        ·
          refine ⟨147317033917846982017557557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98211355945231321345038371 147317033917846982017557557)
          ·
            refine ⟨13810971929798154564146021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147317033917846982017557557 13810971929798154564146021)
            ·
              refine ⟨2589557236837153980777379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13810971929798154564146021 2589557236837153980777379)
              ·
                refine ⟨3884335855255730971166069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589557236837153980777379 3884335855255730971166069)
                ·
                  refine ⟨364156486430224778546819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3884335855255730971166069 364156486430224778546819)
                  ·
                    rfl

theorem cell22_3191365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_3191365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191365 prefixEnd_3191365 := by exact prefixLift 3191365
  have htrace : WordTrace (prefixWord ++ tailWord_3191365) baseStart_3191365 baseEnd_3191365 := by
    simpa [prefixWord, tailWord_3191365, baseEnd_3191365] using wordTrace_append hprefix tailTrace_3191365
  have hstable : (prefixWord ++ tailWord_3191365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191365).length < 2 ^ (prefixWord ++ tailWord_3191365).sum := by decide
  have hdescent : baseEnd_3191365 < baseStart_3191365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191425 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 1, 5]
def baseStart_3191425 : Nat := 118140960795 + 3191425 * 2 ^ 59
def prefixEnd_3191425 : Nat := 4983230072969 + 3 ^ 40 * 3191425 * 2
def baseEnd_3191425 : Nat := 1092489998516854179140273

theorem tailTrace_3191425 : CollatzResearch.WordTrace tailWord_3191425 prefixEnd_3191425 1092489998516854179140273 := by
  unfold tailWord_3191425
  simp only [CollatzResearch.WordTrace]
  refine ⟨116400832463019751841303729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77600554975346501227535819 116400832463019751841303729)
  ·
    refine ⟨87300624347264813880977797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116400832463019751841303729 87300624347264813880977797)
    ·
      refine ⟨16368867065112152602683337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87300624347264813880977797 16368867065112152602683337)
      ·
        refine ⟨12276650298834114452012503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16368867065112152602683337 12276650298834114452012503)
        ·
          refine ⟨18414975448251171678018755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12276650298834114452012503 18414975448251171678018755)
          ·
            refine ⟨27622463172376757517028133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18414975448251171678018755 27622463172376757517028133)
            ·
              refine ⟨5179211844820642034442775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27622463172376757517028133 5179211844820642034442775)
              ·
                refine ⟨7768817767230963051664163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5179211844820642034442775 7768817767230963051664163)
                ·
                  refine ⟨11653226650846444577496245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7768817767230963051664163 11653226650846444577496245)
                  ·
                    refine ⟨1092489998516854179140273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11653226650846444577496245 1092489998516854179140273)
                    ·
                      rfl

theorem cell22_3191425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_3191425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191425 prefixEnd_3191425 := by exact prefixLift 3191425
  have htrace : WordTrace (prefixWord ++ tailWord_3191425) baseStart_3191425 baseEnd_3191425 := by
    simpa [prefixWord, tailWord_3191425, baseEnd_3191425] using wordTrace_append hprefix tailTrace_3191425
  have hstable : (prefixWord ++ tailWord_3191425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191425).length < 2 ^ (prefixWord ++ tailWord_3191425).sum := by decide
  have hdescent : baseEnd_3191425 < baseStart_3191425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191444 : List Nat := [2, 4, 2, 2, 1, 2, 2, 3, 4]
def baseStart_3191444 : Nat := 118140960795 + 3191444 * 2 ^ 59
def prefixEnd_3191444 : Nat := 4983230072969 + 3 ^ 40 * 3191444 * 2
def baseEnd_3191444 : Nat := 364165500868381487638405

theorem tailTrace_3191444 : CollatzResearch.WordTrace tailWord_3191444 prefixEnd_3191444 364165500868381487638405 := by
  unfold tailWord_3191444
  simp only [CollatzResearch.WordTrace]
  refine ⟨58200762724975459043122693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77601016966633945390830257 58200762724975459043122693)
  ·
    refine ⟨10912643010932898570585505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58200762724975459043122693 10912643010932898570585505)
    ·
      refine ⟨8184482258199673927939129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10912643010932898570585505 8184482258199673927939129)
      ·
        refine ⟨6138361693649755445954347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8184482258199673927939129 6138361693649755445954347)
        ·
          refine ⟨9207542540474633168931521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6138361693649755445954347 9207542540474633168931521)
          ·
            refine ⟨6905656905355974876698641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9207542540474633168931521 6905656905355974876698641)
            ·
              refine ⟨5179242679016981157523981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6905656905355974876698641 5179242679016981157523981)
              ·
                refine ⟨1942216004631367934071493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5179242679016981157523981 1942216004631367934071493)
                ·
                  refine ⟨364165500868381487638405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1942216004631367934071493 364165500868381487638405)
                  ·
                    rfl

theorem cell22_3191444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_3191444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191444 prefixEnd_3191444 := by exact prefixLift 3191444
  have htrace : WordTrace (prefixWord ++ tailWord_3191444) baseStart_3191444 baseEnd_3191444 := by
    simpa [prefixWord, tailWord_3191444, baseEnd_3191444] using wordTrace_append hprefix tailTrace_3191444
  have hstable : (prefixWord ++ tailWord_3191444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191444).length < 2 ^ (prefixWord ++ tailWord_3191444).sum := by decide
  have hdescent : baseEnd_3191444 < baseStart_3191444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191500 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 7]
def baseStart_3191500 : Nat := 118140960795 + 3191500 * 2 ^ 59
def prefixEnd_3191500 : Nat := 4983230072969 + 3 ^ 40 * 3191500 * 2
def baseEnd_3191500 : Nat := 364171890849859661171681

theorem tailTrace_3191500 : CollatzResearch.WordTrace tailWord_3191500 prefixEnd_3191500 364171890849859661171681 := by
  unfold tailWord_3191500
  simp only [CollatzResearch.WordTrace]
  refine ⟨58201783968874019825141977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77602378625165359766855969 58201783968874019825141977)
  ·
    refine ⟨43651337976655514868856483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58201783968874019825141977 43651337976655514868856483)
    ·
      refine ⟨65477006964983272303284725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43651337976655514868856483 65477006964983272303284725)
      ·
        refine ⟨6138469402967181778432943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65477006964983272303284725 6138469402967181778432943)
        ·
          refine ⟨9207704104450772667649415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6138469402967181778432943 9207704104450772667649415)
          ·
            refine ⟨13811556156676159001474123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9207704104450772667649415 13811556156676159001474123)
            ·
              refine ⟨20717334235014238502211185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13811556156676159001474123 20717334235014238502211185)
              ·
                refine ⟨15538000676260678876658389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20717334235014238502211185 15538000676260678876658389)
                ·
                  refine ⟨364171890849859661171681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15538000676260678876658389 364171890849859661171681)
                  ·
                    rfl

theorem cell22_3191500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_3191500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191500 prefixEnd_3191500 := by exact prefixLift 3191500
  have htrace : WordTrace (prefixWord ++ tailWord_3191500) baseStart_3191500 baseEnd_3191500 := by
    simpa [prefixWord, tailWord_3191500, baseEnd_3191500] using wordTrace_append hprefix tailTrace_3191500
  have hstable : (prefixWord ++ tailWord_3191500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191500).length < 2 ^ (prefixWord ++ tailWord_3191500).sum := by decide
  have hdescent : baseEnd_3191500 < baseStart_3191500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191521 : List Nat := [1, 2, 3, 1, 4, 2, 3, 2, 1, 3]
def baseStart_3191521 : Nat := 118140960795 + 3191521 * 2 ^ 59
def prefixEnd_3191521 : Nat := 4983230072969 + 3 ^ 40 * 3191521 * 2
def baseEnd_3191521 : Nat := 1092522861278741928739979

theorem tailTrace_3191521 : CollatzResearch.WordTrace tailWord_3191521 prefixEnd_3191521 1092522861278741928739979 := by
  unfold tailWord_3191521
  simp only [CollatzResearch.WordTrace]
  refine ⟨116404333870671960236798417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77602889247114640157865611 116404333870671960236798417)
  ·
    refine ⟨87303250403003970177598813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116404333870671960236798417 87303250403003970177598813)
    ·
      refine ⟨32738718901126488816599555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87303250403003970177598813 32738718901126488816599555)
      ·
        refine ⟨49108078351689733224899333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32738718901126488816599555 49108078351689733224899333)
        ·
          refine ⟨9207764690941824979668625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49108078351689733224899333 9207764690941824979668625)
          ·
            refine ⟨6905823518206368734751469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9207764690941824979668625 6905823518206368734751469)
            ·
              refine ⟨2589683819327388275531801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6905823518206368734751469 2589683819327388275531801)
              ·
                refine ⟨1942262864495541206648851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2589683819327388275531801 1942262864495541206648851)
                ·
                  refine ⟨2913394296743311809973277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1942262864495541206648851 2913394296743311809973277)
                  ·
                    refine ⟨1092522861278741928739979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2913394296743311809973277 1092522861278741928739979)
                    ·
                      rfl

theorem cell22_3191521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_3191521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191521 prefixEnd_3191521 := by exact prefixLift 3191521
  have htrace : WordTrace (prefixWord ++ tailWord_3191521) baseStart_3191521 baseEnd_3191521 := by
    simpa [prefixWord, tailWord_3191521, baseEnd_3191521] using wordTrace_append hprefix tailTrace_3191521
  have hstable : (prefixWord ++ tailWord_3191521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191521).length < 2 ^ (prefixWord ++ tailWord_3191521).sum := by decide
  have hdescent : baseEnd_3191521 < baseStart_3191521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191530 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_3191530 : Nat := 118140960795 + 3191530 * 2 ^ 59
def prefixEnd_3191530 : Nat := 4983230072969 + 3 ^ 40 * 3191530 * 2
def baseEnd_3191530 : Nat := 1092525942162668905264951

theorem tailTrace_3191530 : CollatzResearch.WordTrace tailWord_3191530 prefixEnd_3191530 1092525942162668905264951 := by
  unfold tailWord_3191530
  simp only [CollatzResearch.WordTrace]
  refine ⟨29101165531909838693469011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77603108085092903182584029 29101165531909838693469011)
  ·
    refine ⟨43651748297864758040203517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29101165531909838693469011 43651748297864758040203517)
    ·
      refine ⟨16369405611699284265076319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43651748297864758040203517 16369405611699284265076319)
      ·
        refine ⟨24554108417548926397614479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16369405611699284265076319 24554108417548926397614479)
        ·
          refine ⟨36831162626323389596421719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24554108417548926397614479 36831162626323389596421719)
          ·
            refine ⟨55246743939485084394632579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36831162626323389596421719 55246743939485084394632579)
            ·
              refine ⟨82870115909227626591948869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55246743939485084394632579 82870115909227626591948869)
              ·
                refine ⟨15538146732980179985990413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82870115909227626591948869 15538146732980179985990413)
                ·
                  refine ⟨5826805024867567494746405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15538146732980179985990413 5826805024867567494746405)
                  ·
                    refine ⟨1092525942162668905264951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5826805024867567494746405 1092525942162668905264951)
                    ·
                      rfl

theorem cell22_3191530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_3191530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191530 prefixEnd_3191530 := by exact prefixLift 3191530
  have htrace : WordTrace (prefixWord ++ tailWord_3191530) baseStart_3191530 baseEnd_3191530 := by
    simpa [prefixWord, tailWord_3191530, baseEnd_3191530] using wordTrace_append hprefix tailTrace_3191530
  have hstable : (prefixWord ++ tailWord_3191530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191530).length < 2 ^ (prefixWord ++ tailWord_3191530).sum := by decide
  have hdescent : baseEnd_3191530 < baseStart_3191530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191534 : List Nat := [4, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_3191534 : Nat := 118140960795 + 3191534 * 2 ^ 59
def prefixEnd_3191534 : Nat := 4983230072969 + 3 ^ 40 * 3191534 * 2
def baseEnd_3191534 : Nat := 364175770481471409388313

theorem tailTrace_3191534 : CollatzResearch.WordTrace tailWord_3191534 prefixEnd_3191534 364175770481471409388313 := by
  unfold tailWord_3191534
  simp only [CollatzResearch.WordTrace]
  refine ⟨14550601002453107932127707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77603205346416575638014437 14550601002453107932127707)
  ·
    refine ⟨21825901503679661898191561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14550601002453107932127707 21825901503679661898191561)
    ·
      refine ⟨16369426127759746423643671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21825901503679661898191561 16369426127759746423643671)
      ·
        refine ⟨24554139191639619635465507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16369426127759746423643671 24554139191639619635465507)
        ·
          refine ⟨36831208787459429453198261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24554139191639619635465507 36831208787459429453198261)
          ·
            refine ⟨3452925823824321511237337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36831208787459429453198261 3452925823824321511237337)
            ·
              refine ⟨2589694367868241133428003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3452925823824321511237337 2589694367868241133428003)
              ·
                refine ⟨3884541551802361700142005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589694367868241133428003 3884541551802361700142005)
                ·
                  refine ⟨364175770481471409388313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3884541551802361700142005 364175770481471409388313)
                  ·
                    rfl

theorem cell22_3191534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_3191534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191534 prefixEnd_3191534 := by exact prefixLift 3191534
  have htrace : WordTrace (prefixWord ++ tailWord_3191534) baseStart_3191534 baseEnd_3191534 := by
    simpa [prefixWord, tailWord_3191534, baseEnd_3191534] using wordTrace_append hprefix tailTrace_3191534
  have hstable : (prefixWord ++ tailWord_3191534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191534).length < 2 ^ (prefixWord ++ tailWord_3191534).sum := by decide
  have hdescent : baseEnd_3191534 < baseStart_3191534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191560 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 3, 5]
def baseStart_3191560 : Nat := 118140960795 + 3191560 * 2 ^ 59
def prefixEnd_3191560 : Nat := 4983230072969 + 3 ^ 40 * 3191560 * 2
def baseEnd_3191560 : Nat := 1092536211775758827014859

theorem tailTrace_3191560 : CollatzResearch.WordTrace tailWord_3191560 prefixEnd_3191560 1092536211775758827014859 := by
  unfold tailWord_3191560
  simp only [CollatzResearch.WordTrace]
  refine ⟨58202878158765334948734067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77603837545020446598312089 58202878158765334948734067)
  ·
    refine ⟨87304317238148002423101101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58202878158765334948734067 87304317238148002423101101)
    ·
      refine ⟨32739118964305500908662913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87304317238148002423101101 32739118964305500908662913)
      ·
        refine ⟨24554339223229125681497185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32739118964305500908662913 24554339223229125681497185)
        ·
          refine ⟨18415754417421844261122889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24554339223229125681497185 18415754417421844261122889)
          ·
            refine ⟨13811815813066383195842167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18415754417421844261122889 13811815813066383195842167)
            ·
              refine ⟨20717723719599574793763251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13811815813066383195842167 20717723719599574793763251)
              ·
                refine ⟨31076585579399362190644877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20717723719599574793763251 31076585579399362190644877)
                ·
                  refine ⟨11653719592274760821491829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31076585579399362190644877 11653719592274760821491829)
                  ·
                    refine ⟨1092536211775758827014859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11653719592274760821491829 1092536211775758827014859)
                    ·
                      rfl

theorem cell22_3191560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_3191560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191560 prefixEnd_3191560 := by exact prefixLift 3191560
  have htrace : WordTrace (prefixWord ++ tailWord_3191560) baseStart_3191560 baseEnd_3191560 := by
    simpa [prefixWord, tailWord_3191560, baseEnd_3191560] using wordTrace_append hprefix tailTrace_3191560
  have hstable : (prefixWord ++ tailWord_3191560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191560).length < 2 ^ (prefixWord ++ tailWord_3191560).sum := by decide
  have hdescent : baseEnd_3191560 < baseStart_3191560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191562 : List Nat := [3, 1, 2, 2, 1, 2, 2, 5, 4]
def baseStart_3191562 : Nat := 118140960795 + 3191562 * 2 ^ 59
def prefixEnd_3191562 : Nat := 4983230072969 + 3 ^ 40 * 3191562 * 2
def baseEnd_3191562 : Nat := 364178965472210496154951

theorem tailTrace_3191562 : CollatzResearch.WordTrace tailWord_3191562 prefixEnd_3191562 364178965472210496154951 := by
  unfold tailWord_3191562
  simp only [CollatzResearch.WordTrace]
  refine ⟨29101457315880856059760235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77603886175682282826027293 29101457315880856059760235)
  ·
    refine ⟨43652185973821284089640353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29101457315880856059760235 43652185973821284089640353)
    ·
      refine ⟨32739139480365963067230265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43652185973821284089640353 32739139480365963067230265)
      ·
        refine ⟨24554354610274472300422699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32739139480365963067230265 24554354610274472300422699)
        ·
          refine ⟨36831531915411708450634049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24554354610274472300422699 36831531915411708450634049)
          ·
            refine ⟨27623648936558781337975537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36831531915411708450634049 27623648936558781337975537)
            ·
              refine ⟨20717736702419086003481653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27623648936558781337975537 20717736702419086003481653)
              ·
                refine ⟨1942287815851789312826405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20717736702419086003481653 1942287815851789312826405)
                ·
                  refine ⟨364178965472210496154951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1942287815851789312826405 364178965472210496154951)
                  ·
                    rfl

theorem cell22_3191562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_3191562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191562 prefixEnd_3191562 := by exact prefixLift 3191562
  have htrace : WordTrace (prefixWord ++ tailWord_3191562) baseStart_3191562 baseEnd_3191562 := by
    simpa [prefixWord, tailWord_3191562, baseEnd_3191562] using wordTrace_append hprefix tailTrace_3191562
  have hstable : (prefixWord ++ tailWord_3191562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191562).length < 2 ^ (prefixWord ++ tailWord_3191562).sum := by decide
  have hdescent : baseEnd_3191562 < baseStart_3191562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191639 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 3, 3]
def baseStart_3191639 : Nat := 118140960795 + 3191639 * 2 ^ 59
def prefixEnd_3191639 : Nat := 4983230072969 + 3 ^ 40 * 3191639 * 2
def baseEnd_3191639 : Nat := 1092563255090228954289617

theorem tailTrace_3191639 : CollatzResearch.WordTrace tailWord_3191639 prefixEnd_3191639 1092563255090228954289617 := by
  unfold tailWord_3191639
  simp only [CollatzResearch.WordTrace]
  refine ⟨116408637684244466389593971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77605758456162977593062647 116408637684244466389593971)
  ·
    refine ⟨174612956526366699584390957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116408637684244466389593971 174612956526366699584390957)
    ·
      refine ⟨65479858697387512344146609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174612956526366699584390957 65479858697387512344146609)
      ·
        refine ⟨49109894023040634258109957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65479858697387512344146609 49109894023040634258109957)
        ·
          refine ⟨9208105129320118923395617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49109894023040634258109957 9208105129320118923395617)
          ·
            refine ⟨6906078846990089192546713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9208105129320118923395617 6906078846990089192546713)
            ·
              refine ⟨5179559135242566894410035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6906078846990089192546713 5179559135242566894410035)
              ·
                refine ⟨7769338702863850341615053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5179559135242566894410035 7769338702863850341615053)
                ·
                  refine ⟨2913502013573943878105645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7769338702863850341615053 2913502013573943878105645)
                  ·
                    refine ⟨1092563255090228954289617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2913502013573943878105645 1092563255090228954289617)
                    ·
                      rfl

theorem cell22_3191639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_3191639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191639 prefixEnd_3191639 := by exact prefixLift 3191639
  have htrace : WordTrace (prefixWord ++ tailWord_3191639) baseStart_3191639 baseEnd_3191639 := by
    simpa [prefixWord, tailWord_3191639, baseEnd_3191639] using wordTrace_append hprefix tailTrace_3191639
  have hstable : (prefixWord ++ tailWord_3191639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191639).length < 2 ^ (prefixWord ++ tailWord_3191639).sum := by decide
  have hdescent : baseEnd_3191639 < baseStart_3191639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191729 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 1, 5]
def baseStart_3191729 : Nat := 118140960795 + 3191729 * 2 ^ 59
def prefixEnd_3191729 : Nat := 4983230072969 + 3 ^ 40 * 3191729 * 2
def baseEnd_3191729 : Nat := 1092594063929498719539341

theorem tailTrace_3191729 : CollatzResearch.WordTrace tailWord_3191729 prefixEnd_3191729 1092594063929498719539341 := by
  unfold tailWord_3191729
  simp only [CollatzResearch.WordTrace]
  refine ⟨116411920253918411760370241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77607946835945607840246827 116411920253918411760370241)
  ·
    refine ⟨87308940190438808820277681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116411920253918411760370241 87308940190438808820277681)
    ·
      refine ⟨65481705142829106615208261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87308940190438808820277681 65481705142829106615208261)
      ·
        refine ⟨12277819714280457490351549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65481705142829106615208261 12277819714280457490351549)
        ·
          refine ⟨4604182392855171558881831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12277819714280457490351549 4604182392855171558881831)
          ·
            refine ⟨6906273589282757338322747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4604182392855171558881831 6906273589282757338322747)
            ·
              refine ⟨10359410383924136007484121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6906273589282757338322747 10359410383924136007484121)
              ·
                refine ⟨7769557787943102005613091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10359410383924136007484121 7769557787943102005613091)
                ·
                  refine ⟨11654336681914653008419637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7769557787943102005613091 11654336681914653008419637)
                  ·
                    refine ⟨1092594063929498719539341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11654336681914653008419637 1092594063929498719539341)
                    ·
                      rfl

theorem cell22_3191729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_3191729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191729 prefixEnd_3191729 := by exact prefixLift 3191729
  have htrace : WordTrace (prefixWord ++ tailWord_3191729) baseStart_3191729 baseEnd_3191729 := by
    simpa [prefixWord, tailWord_3191729, baseEnd_3191729] using wordTrace_append hprefix tailTrace_3191729
  have hstable : (prefixWord ++ tailWord_3191729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191729).length < 2 ^ (prefixWord ++ tailWord_3191729).sum := by decide
  have hdescent : baseEnd_3191729 < baseStart_3191729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191748 : List Nat := [2, 3, 3, 3, 1, 1, 1, 4, 4]
def baseStart_3191748 : Nat := 118140960795 + 3191748 * 2 ^ 59
def prefixEnd_3191748 : Nat := 4983230072969 + 3 ^ 40 * 3191748 * 2
def baseEnd_3191748 : Nat := 364200189339263001104761

theorem tailTrace_3191748 : CollatzResearch.WordTrace tailWord_3191748 prefixEnd_3191748 364200189339263001104761 := by
  unfold tailWord_3191748
  simp only [CollatzResearch.WordTrace]
  refine ⟨58206306620424789002655949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77608408827233052003541265 58206306620424789002655949)
  ·
    refine ⟨21827364982659295875995981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58206306620424789002655949 21827364982659295875995981)
    ·
      refine ⟨8185261868497235953498493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21827364982659295875995981 8185261868497235953498493)
      ·
        refine ⟨3069473200686463482561935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8185261868497235953498493 3069473200686463482561935)
        ·
          refine ⟨4604209801029695223842903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3069473200686463482561935 4604209801029695223842903)
          ·
            refine ⟨6906314701544542835764355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4604209801029695223842903 6906314701544542835764355)
            ·
              refine ⟨10359472052316814253646533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6906314701544542835764355 10359472052316814253646533)
              ·
                refine ⟨1942401009809402672558725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10359472052316814253646533 1942401009809402672558725)
                ·
                  refine ⟨364200189339263001104761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1942401009809402672558725 364200189339263001104761)
                  ·
                    rfl

theorem cell22_3191748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_3191748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191748 prefixEnd_3191748 := by exact prefixLift 3191748
  have htrace : WordTrace (prefixWord ++ tailWord_3191748) baseStart_3191748 baseEnd_3191748 := by
    simpa [prefixWord, tailWord_3191748, baseEnd_3191748] using wordTrace_append hprefix tailTrace_3191748
  have hstable : (prefixWord ++ tailWord_3191748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191748).length < 2 ^ (prefixWord ++ tailWord_3191748).sum := by decide
  have hdescent : baseEnd_3191748 < baseStart_3191748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191778 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_3191778 : Nat := 118140960795 + 3191778 * 2 ^ 59
def prefixEnd_3191778 : Nat := 4983230072969 + 3 ^ 40 * 3191778 * 2
def baseEnd_3191778 : Nat := 1092610837630878925064191

theorem tailTrace_3191778 : CollatzResearch.WordTrace tailWord_3191778 prefixEnd_3191778 1092610837630878925064191 := by
  unfold tailWord_3191778
  simp only [CollatzResearch.WordTrace]
  refine ⟨29103426857685223282225997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77609138287160595419269325 29103426857685223282225997)
  ·
    refine ⟨10913785071631958730834749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29103426857685223282225997 10913785071631958730834749)
    ·
      refine ⟨4092669401861984524063031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10913785071631958730834749 4092669401861984524063031)
      ·
        refine ⟨6139004102792976786094547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4092669401861984524063031 6139004102792976786094547)
        ·
          refine ⟨9208506154189465179141821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6139004102792976786094547 9208506154189465179141821)
          ·
            refine ⟨3453189807821049442178183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9208506154189465179141821 3453189807821049442178183)
            ·
              refine ⟨5179784711731574163267275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3453189807821049442178183 5179784711731574163267275)
              ·
                refine ⟨7769677067597361244900913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5179784711731574163267275 7769677067597361244900913)
                ·
                  refine ⟨5827257800698020933675685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7769677067597361244900913 5827257800698020933675685)
                  ·
                    refine ⟨1092610837630878925064191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5827257800698020933675685 1092610837630878925064191)
                    ·
                      rfl

theorem cell22_3191778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_3191778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191778 prefixEnd_3191778 := by exact prefixLift 3191778
  have htrace : WordTrace (prefixWord ++ tailWord_3191778) baseStart_3191778 baseEnd_3191778 := by
    simpa [prefixWord, tailWord_3191778, baseEnd_3191778] using wordTrace_append hprefix tailTrace_3191778
  have hstable : (prefixWord ++ tailWord_3191778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191778).length < 2 ^ (prefixWord ++ tailWord_3191778).sum := by decide
  have hdescent : baseEnd_3191778 < baseStart_3191778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191791 : List Nat := [1, 1, 2, 1, 4, 3, 1, 5, 1, 3]
def baseStart_3191791 : Nat := 118140960795 + 3191791 * 2 ^ 59
def prefixEnd_3191791 : Nat := 4983230072969 + 3 ^ 40 * 3191791 * 2
def baseEnd_3191791 : Nat := 1092615287796551224489151

theorem tailTrace_3191791 : CollatzResearch.WordTrace tailWord_3191791 prefixEnd_3191791 1092615287796551224489151 := by
  unfold tailWord_3191791
  simp only [CollatzResearch.WordTrace]
  refine ⟨116414181579693796349127227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77609454386462530899418151 116414181579693796349127227)
  ·
    refine ⟨174621272369540694523690841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116414181579693796349127227 174621272369540694523690841)
    ·
      refine ⟨130965954277155520892768131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174621272369540694523690841 130965954277155520892768131)
      ·
        refine ⟨196448931415733281339152197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130965954277155520892768131 196448931415733281339152197)
        ·
          refine ⟨36834174640449990251091037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196448931415733281339152197 36834174640449990251091037)
          ·
            refine ⟨13812815490168746344159139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36834174640449990251091037 13812815490168746344159139)
            ·
              refine ⟨20719223235253119516238709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13812815490168746344159139 20719223235253119516238709)
              ·
                refine ⟨1942427178304979954647379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20719223235253119516238709 1942427178304979954647379)
                ·
                  refine ⟨2913640767457469931971069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1942427178304979954647379 2913640767457469931971069)
                  ·
                    refine ⟨1092615287796551224489151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2913640767457469931971069 1092615287796551224489151)
                    ·
                      rfl

theorem cell22_3191791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 1, 3].length) (baseStart_3191791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191791 prefixEnd_3191791 := by exact prefixLift 3191791
  have htrace : WordTrace (prefixWord ++ tailWord_3191791) baseStart_3191791 baseEnd_3191791 := by
    simpa [prefixWord, tailWord_3191791, baseEnd_3191791] using wordTrace_append hprefix tailTrace_3191791
  have hstable : (prefixWord ++ tailWord_3191791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191791).length < 2 ^ (prefixWord ++ tailWord_3191791).sum := by decide
  have hdescent : baseEnd_3191791 < baseStart_3191791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191797 : List Nat := [1, 3, 5, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3191797 : Nat := 118140960795 + 3191797 * 2 ^ 59
def prefixEnd_3191797 : Nat := 4983230072969 + 3 ^ 40 * 3191797 * 2
def baseEnd_3191797 : Nat := 1092617341719169208839133

theorem tailTrace_3191797 : CollatzResearch.WordTrace tailWord_3191797 prefixEnd_3191797 1092617341719169208839133 := by
  unfold tailWord_3191797
  simp only [CollatzResearch.WordTrace]
  refine ⟨116414400417672059373845645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77609600278448039582563763 116414400417672059373845645)
  ·
    refine ⟨43655400156627022265192117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116414400417672059373845645 43655400156627022265192117)
    ·
      refine ⟨4092693764683783337361761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43655400156627022265192117 4092693764683783337361761)
      ·
        refine ⟨3069520323512837503021321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4092693764683783337361761 3069520323512837503021321)
        ·
          refine ⟨2302140242634628127265991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3069520323512837503021321 2302140242634628127265991)
          ·
            refine ⟨3453210363951942190898987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2302140242634628127265991 3453210363951942190898987)
            ·
              refine ⟨5179815545927913286348481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3453210363951942190898987 5179815545927913286348481)
              ·
                refine ⟨3884861659445934964761361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5179815545927913286348481 3884861659445934964761361)
                ·
                  refine ⟨2913646244584451223571021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3884861659445934964761361 2913646244584451223571021)
                  ·
                    refine ⟨1092617341719169208839133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2913646244584451223571021 1092617341719169208839133)
                    ·
                      rfl

theorem cell22_3191797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3191797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191797 prefixEnd_3191797 := by exact prefixLift 3191797
  have htrace : WordTrace (prefixWord ++ tailWord_3191797) baseStart_3191797 baseEnd_3191797 := by
    simpa [prefixWord, tailWord_3191797, baseEnd_3191797] using wordTrace_append hprefix tailTrace_3191797
  have hstable : (prefixWord ++ tailWord_3191797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191797).length < 2 ^ (prefixWord ++ tailWord_3191797).sum := by decide
  have hdescent : baseEnd_3191797 < baseStart_3191797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191804 : List Nat := [2, 2, 2, 1, 2, 3, 3, 2, 5]
def baseStart_3191804 : Nat := 118140960795 + 3191804 * 2 ^ 59
def prefixEnd_3191804 : Nat := 4983230072969 + 3 ^ 40 * 3191804 * 2
def baseEnd_3191804 : Nat := 364206579320741174638037

theorem tailTrace_3191804 : CollatzResearch.WordTrace tailWord_3191804 prefixEnd_3191804 364206579320741174638037 := by
  unfold tailWord_3191804
  simp only [CollatzResearch.WordTrace]
  refine ⟨58207327864323349784675233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77609770485764466379566977 58207327864323349784675233)
  ·
    refine ⟨43655495898242512338506425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58207327864323349784675233 43655495898242512338506425)
    ·
      refine ⟨32741621923681884253879819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43655495898242512338506425 32741621923681884253879819)
      ·
        refine ⟨49112432885522826380819729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32741621923681884253879819 49112432885522826380819729)
        ·
          refine ⟨36834324664142119785614797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49112432885522826380819729 36834324664142119785614797)
          ·
            refine ⟨13812871749053294919605549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36834324664142119785614797 13812871749053294919605549)
            ·
              refine ⟨5179826905894985594852081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13812871749053294919605549 5179826905894985594852081)
              ·
                refine ⟨3884870179421239196139061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5179826905894985594852081 3884870179421239196139061)
                ·
                  refine ⟨364206579320741174638037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3884870179421239196139061 364206579320741174638037)
                  ·
                    rfl

theorem cell22_3191804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_3191804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191804 prefixEnd_3191804 := by exact prefixLift 3191804
  have htrace : WordTrace (prefixWord ++ tailWord_3191804) baseStart_3191804 baseEnd_3191804 := by
    simpa [prefixWord, tailWord_3191804, baseEnd_3191804] using wordTrace_append hprefix tailTrace_3191804
  have hstable : (prefixWord ++ tailWord_3191804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191804).length < 2 ^ (prefixWord ++ tailWord_3191804).sum := by decide
  have hdescent : baseEnd_3191804 < baseStart_3191804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191817 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 5, 4]
def baseStart_3191817 : Nat := 118140960795 + 3191817 * 2 ^ 59
def prefixEnd_3191817 : Nat := 4983230072969 + 3 ^ 40 * 3191817 * 2
def baseEnd_3191817 : Nat := 1092624188127895823339071

theorem tailTrace_3191817 : CollatzResearch.WordTrace tailWord_3191817 prefixEnd_3191817 1092624188127895823339071 := by
  unfold tailWord_3191817
  simp only [CollatzResearch.WordTrace]
  refine ⟨116415129877599602789573705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77610086585066401859715803 116415129877599602789573705)
  ·
    refine ⟨87311347408199702092180279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116415129877599602789573705 87311347408199702092180279)
    ·
      refine ⟨130967021112299553138270419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87311347408199702092180279 130967021112299553138270419)
      ·
        refine ⟨196450531668449329707405629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130967021112299553138270419 196450531668449329707405629)
        ·
          refine ⟨73668949375668498640277111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196450531668449329707405629 73668949375668498640277111)
          ·
            refine ⟨110503424063502747960415667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73668949375668498640277111 110503424063502747960415667)
            ·
              refine ⟨165755136095254121940623501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110503424063502747960415667 165755136095254121940623501)
              ·
                refine ⟨62158176035720295727733813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165755136095254121940623501 62158176035720295727733813)
                ·
                  refine ⟨5827329003348777724475045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62158176035720295727733813 5827329003348777724475045)
                  ·
                    refine ⟨1092624188127895823339071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5827329003348777724475045 1092624188127895823339071)
                    ·
                      rfl

theorem cell22_3191817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_3191817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191817 prefixEnd_3191817 := by exact prefixLift 3191817
  have htrace : WordTrace (prefixWord ++ tailWord_3191817) baseStart_3191817 baseEnd_3191817 := by
    simpa [prefixWord, tailWord_3191817, baseEnd_3191817] using wordTrace_append hprefix tailTrace_3191817
  have hstable : (prefixWord ++ tailWord_3191817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191817).length < 2 ^ (prefixWord ++ tailWord_3191817).sum := by decide
  have hdescent : baseEnd_3191817 < baseStart_3191817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191877 : List Nat := [1, 3, 1, 1, 1, 3, 3, 9]
def baseStart_3191877 : Nat := 118140960795 + 3191877 * 2 ^ 59
def prefixEnd_3191877 : Nat := 4983230072969 + 3 ^ 40 * 3191877 * 2
def baseEnd_3191877 : Nat := 121404969706008407426543

theorem tailTrace_3191877 : CollatzResearch.WordTrace tailWord_3191877 prefixEnd_3191877 121404969706008407426543 := by
  unfold tailWord_3191877
  simp only [CollatzResearch.WordTrace]
  refine ⟨116417318257382233036757885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77611545504921488691171923 116417318257382233036757885)
  ·
    refine ⟨43656494346518337388784207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116417318257382233036757885 43656494346518337388784207)
    ·
      refine ⟨65484741519777506083176311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43656494346518337388784207 65484741519777506083176311)
      ·
        refine ⟨98227112279666259124764467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65484741519777506083176311 98227112279666259124764467)
        ·
          refine ⟨147340668419499388687146701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98227112279666259124764467 147340668419499388687146701)
          ·
            refine ⟨55252750657312270757680013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147340668419499388687146701 55252750657312270757680013)
            ·
              refine ⟨20719781496492101534130005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55252750657312270757680013 20719781496492101534130005)
              ·
                refine ⟨121404969706008407426543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20719781496492101534130005 121404969706008407426543)
                ·
                  rfl

theorem cell22_3191877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 9].length) (baseStart_3191877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191877 prefixEnd_3191877 := by exact prefixLift 3191877
  have htrace : WordTrace (prefixWord ++ tailWord_3191877) baseStart_3191877 baseEnd_3191877 := by
    simpa [prefixWord, tailWord_3191877, baseEnd_3191877] using wordTrace_append hprefix tailTrace_3191877
  have hstable : (prefixWord ++ tailWord_3191877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191877).length < 2 ^ (prefixWord ++ tailWord_3191877).sum := by decide
  have hdescent : baseEnd_3191877 < baseStart_3191877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191902 : List Nat := [4, 4, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_3191902 : Nat := 118140960795 + 3191902 * 2 ^ 59
def prefixEnd_3191902 : Nat := 4983230072969 + 3 ^ 40 * 3191902 * 2
def baseEnd_3191902 : Nat := 1092653285364983934963811

theorem tailTrace_3191902 : CollatzResearch.WordTrace tailWord_3191902 prefixEnd_3191902 1092653285364983934963811 := by
  unfold tailWord_3191902
  simp only [CollatzResearch.WordTrace]
  refine ⟨14552278760286457788302245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77612153388194441537611973 14552278760286457788302245)
  ·
    refine ⟨2728552267553710835306671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14552278760286457788302245 2728552267553710835306671)
    ·
      refine ⟨4092828401330566252960007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2728552267553710835306671 4092828401330566252960007)
      ·
        refine ⟨6139242601995849379440011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4092828401330566252960007 6139242601995849379440011)
        ·
          refine ⟨9208863902993774069160017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6139242601995849379440011 9208863902993774069160017)
          ·
            refine ⟨6906647927245330551870013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9208863902993774069160017 6906647927245330551870013)
            ·
              refine ⟨2589992972716998956951255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6906647927245330551870013 2589992972716998956951255)
              ·
                refine ⟨3884989459075498435426883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589992972716998956951255 3884989459075498435426883)
                ·
                  refine ⟨5827484188613247653140325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3884989459075498435426883 5827484188613247653140325)
                  ·
                    refine ⟨1092653285364983934963811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5827484188613247653140325 1092653285364983934963811)
                    ·
                      rfl

theorem cell22_3191902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_3191902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191902 prefixEnd_3191902 := by exact prefixLift 3191902
  have htrace : WordTrace (prefixWord ++ tailWord_3191902) baseStart_3191902 baseEnd_3191902 := by
    simpa [prefixWord, tailWord_3191902, baseEnd_3191902] using wordTrace_append hprefix tailTrace_3191902
  have hstable : (prefixWord ++ tailWord_3191902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191902).length < 2 ^ (prefixWord ++ tailWord_3191902).sum := by decide
  have hdescent : baseEnd_3191902 < baseStart_3191902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191939 : List Nat := [1, 1, 1, 3, 3, 2, 1, 5, 5]
def baseStart_3191939 : Nat := 118140960795 + 3191939 * 2 ^ 59
def prefixEnd_3191939 : Nat := 4983230072969 + 3 ^ 40 * 3191939 * 2
def baseEnd_3191939 : Nat := 364221983740376057262899

theorem tailTrace_3191939 : CollatzResearch.WordTrace tailWord_3191939 prefixEnd_3191939 364221983740376057262899 := by
  unfold tailWord_3191939
  simp only [CollatzResearch.WordTrace]
  refine ⟨116419579583157617625514871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77613053055438411750343247 116419579583157617625514871)
  ·
    refine ⟨174629369374736426438272307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116419579583157617625514871 174629369374736426438272307)
    ·
      refine ⟨261944054062104639657408461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174629369374736426438272307 261944054062104639657408461)
      ·
        refine ⟨98229020273289239871528173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261944054062104639657408461 98229020273289239871528173)
        ·
          refine ⟨36835882602483464951823065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98229020273289239871528173 36835882602483464951823065)
          ·
            refine ⟨27626911951862598713867299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36835882602483464951823065 27626911951862598713867299)
            ·
              refine ⟨41440367927793898070800949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27626911951862598713867299 41440367927793898070800949)
              ·
                refine ⟨3885034493230677944137589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41440367927793898070800949 3885034493230677944137589)
                ·
                  refine ⟨364221983740376057262899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3885034493230677944137589 364221983740376057262899)
                  ·
                    rfl

theorem cell22_3191939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 5].length) (baseStart_3191939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191939 prefixEnd_3191939 := by exact prefixLift 3191939
  have htrace : WordTrace (prefixWord ++ tailWord_3191939) baseStart_3191939 baseEnd_3191939 := by
    simpa [prefixWord, tailWord_3191939, baseEnd_3191939] using wordTrace_append hprefix tailTrace_3191939
  have hstable : (prefixWord ++ tailWord_3191939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191939).length < 2 ^ (prefixWord ++ tailWord_3191939).sum := by decide
  have hdescent : baseEnd_3191939 < baseStart_3191939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191960 : List Nat := [2, 1, 2, 4, 2, 2, 2, 3, 1, 3]
def baseStart_3191960 : Nat := 118140960795 + 3191960 * 2 ^ 59
def prefixEnd_3191960 : Nat := 4983230072969 + 3 ^ 40 * 3191960 * 2
def baseEnd_3191960 : Nat := 1092673139950291117013633

theorem tailTrace_3191960 : CollatzResearch.WordTrace tailWord_3191960 prefixEnd_3191960 1092673139950291117013633 := by
  unfold tailWord_3191960
  simp only [CollatzResearch.WordTrace]
  refine ⟨58210172758040769106014667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77613563677387692141352889 58210172758040769106014667)
  ·
    refine ⟨87315259137061153659022001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58210172758040769106014667 87315259137061153659022001)
    ·
      refine ⟨65486444352795865244266501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87315259137061153659022001 65486444352795865244266501)
      ·
        refine ⟨12278708316149224733299969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65486444352795865244266501 12278708316149224733299969)
        ·
          refine ⟨9209031237111918549974977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12278708316149224733299969 9209031237111918549974977)
          ·
            refine ⟨6906773427833938912481233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9209031237111918549974977 6906773427833938912481233)
            ·
              refine ⟨5180080070875454184360925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6906773427833938912481233 5180080070875454184360925)
              ·
                refine ⟨1942530026578295319135347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5180080070875454184360925 1942530026578295319135347)
                ·
                  refine ⟨2913795039867442978703021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1942530026578295319135347 2913795039867442978703021)
                  ·
                    refine ⟨1092673139950291117013633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2913795039867442978703021 1092673139950291117013633)
                    ·
                      rfl

theorem cell22_3191960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_3191960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3191960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3191960 prefixEnd_3191960 := by exact prefixLift 3191960
  have htrace : WordTrace (prefixWord ++ tailWord_3191960) baseStart_3191960 baseEnd_3191960 := by
    simpa [prefixWord, tailWord_3191960, baseEnd_3191960] using wordTrace_append hprefix tailTrace_3191960
  have hstable : (prefixWord ++ tailWord_3191960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191960).length < 2 ^ (prefixWord ++ tailWord_3191960).sum := by decide
  have hdescent : baseEnd_3191960 < baseStart_3191960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192050 : List Nat := [3, 2, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_3192050 : Nat := 118140960795 + 3192050 * 2 ^ 59
def prefixEnd_3192050 : Nat := 4983230072969 + 3 ^ 40 * 3192050 * 2
def baseEnd_3192050 : Nat := 1092703948789560882263357

theorem tailTrace_3192050 : CollatzResearch.WordTrace tailWord_3192050 prefixEnd_3192050 1092703948789560882263357 := by
  unfold tailWord_3192050
  simp only [CollatzResearch.WordTrace]
  refine ⟨29105907021438870895701401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77615752057170322388537069 29105907021438870895701401)
  ·
    refine ⟨21829430266079153171776051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29105907021438870895701401 21829430266079153171776051)
    ·
      refine ⟨32744145399118729757664077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21829430266079153171776051 32744145399118729757664077)
      ·
        refine ⟨12279054524669523659124029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32744145399118729757664077 12279054524669523659124029)
        ·
          refine ⟨4604645446751071372171511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12279054524669523659124029 4604645446751071372171511)
          ·
            refine ⟨6906968170126607058257267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4604645446751071372171511 6906968170126607058257267)
            ·
              refine ⟨10360452255189910587385901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6906968170126607058257267 10360452255189910587385901)
              ·
                refine ⟨3885169595696216470269713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10360452255189910587385901 3885169595696216470269713)
                ·
                  refine ⟨2913877196772162352702285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3885169595696216470269713 2913877196772162352702285)
                  ·
                    refine ⟨1092703948789560882263357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2913877196772162352702285 1092703948789560882263357)
                    ·
                      rfl

theorem cell22_3192050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_3192050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192050 prefixEnd_3192050 := by exact prefixLift 3192050
  have htrace : WordTrace (prefixWord ++ tailWord_3192050) baseStart_3192050 baseEnd_3192050 := by
    simpa [prefixWord, tailWord_3192050, baseEnd_3192050] using wordTrace_append hprefix tailTrace_3192050
  have hstable : (prefixWord ++ tailWord_3192050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192050).length < 2 ^ (prefixWord ++ tailWord_3192050).sum := by decide
  have hdescent : baseEnd_3192050 < baseStart_3192050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192089 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 5, 7]
def baseStart_3192089 : Nat := 118140960795 + 3192089 * 2 ^ 59
def prefixEnd_3192089 : Nat := 4983230072969 + 3 ^ 40 * 3192089 * 2
def baseEnd_3192089 : Nat := 1092717299286577780538237

theorem tailTrace_3192089 : CollatzResearch.WordTrace tailWord_3192089 prefixEnd_3192089 1092717299286577780538237 := by
  unfold tailWord_3192089
  simp only [CollatzResearch.WordTrace]
  refine ⟨116425050532614193243475321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77616700355076128828983547 116425050532614193243475321)
  ·
    refine ⟨87318787899460644932606491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116425050532614193243475321 87318787899460644932606491)
    ·
      refine ⟨130978181849190967398909737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87318787899460644932606491 130978181849190967398909737)
      ·
        refine ⟨98233636386893225549182303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130978181849190967398909737 98233636386893225549182303)
        ·
          refine ⟨147350454580339838323773455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98233636386893225549182303 147350454580339838323773455)
          ·
            refine ⟨221025681870509757485660183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147350454580339838323773455 221025681870509757485660183)
            ·
              refine ⟨331538522805764636228490275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221025681870509757485660183 331538522805764636228490275)
              ·
                refine ⟨497307784208646954342735413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331538522805764636228490275 497307784208646954342735413)
                ·
                  refine ⟨46622604769560651969631445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 497307784208646954342735413 46622604769560651969631445)
                  ·
                    refine ⟨1092717299286577780538237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46622604769560651969631445 1092717299286577780538237)
                    ·
                      rfl

theorem cell22_3192089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_3192089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192089 prefixEnd_3192089 := by exact prefixLift 3192089
  have htrace : WordTrace (prefixWord ++ tailWord_3192089) baseStart_3192089 baseEnd_3192089 := by
    simpa [prefixWord, tailWord_3192089, baseEnd_3192089] using wordTrace_append hprefix tailTrace_3192089
  have hstable : (prefixWord ++ tailWord_3192089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192089).length < 2 ^ (prefixWord ++ tailWord_3192089).sum := by decide
  have hdescent : baseEnd_3192089 < baseStart_3192089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192153 : List Nat := [1, 2, 1, 2, 2, 2, 4, 4, 4]
def baseStart_3192153 : Nat := 118140960795 + 3192153 * 2 ^ 59
def prefixEnd_3192153 : Nat := 4983230072969 + 3 ^ 40 * 3192153 * 2
def baseEnd_3192153 : Nat := 364246402598167648979347

theorem tailTrace_3192153 : CollatzResearch.WordTrace tailWord_3192153 prefixEnd_3192153 364246402598167648979347 := by
  unfold tailWord_3192153
  simp only [CollatzResearch.WordTrace]
  refine ⟨116427384804382332173805113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77618256536254888115870075 116427384804382332173805113)
  ·
    refine ⟨87320538603286749130353835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116427384804382332173805113 87320538603286749130353835)
    ·
      refine ⟨130980807904930123695530753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87320538603286749130353835 130980807904930123695530753)
      ·
        refine ⟨98235605928697592771648065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130980807904930123695530753 98235605928697592771648065)
        ·
          refine ⟨73676704446523194578736049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98235605928697592771648065 73676704446523194578736049)
          ·
            refine ⟨55257528334892395934052037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73676704446523194578736049 55257528334892395934052037)
            ·
              refine ⟨10360786562792324237634757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55257528334892395934052037 10360786562792324237634757)
              ·
                refine ⟨1942647480523560794556517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10360786562792324237634757 1942647480523560794556517)
                ·
                  refine ⟨364246402598167648979347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1942647480523560794556517 364246402598167648979347)
                  ·
                    rfl

theorem cell22_3192153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 4].length) (baseStart_3192153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192153 prefixEnd_3192153 := by exact prefixLift 3192153
  have htrace : WordTrace (prefixWord ++ tailWord_3192153) baseStart_3192153 baseEnd_3192153 := by
    simpa [prefixWord, tailWord_3192153, baseEnd_3192153] using wordTrace_append hprefix tailTrace_3192153
  have hstable : (prefixWord ++ tailWord_3192153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192153).length < 2 ^ (prefixWord ++ tailWord_3192153).sum := by decide
  have hdescent : baseEnd_3192153 < baseStart_3192153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192260 : List Nat := [2, 3, 3, 2, 1, 1, 1, 4, 5]
def baseStart_3192260 : Nat := 118140960795 + 3192260 * 2 ^ 59
def prefixEnd_3192260 : Nat := 4983230072969 + 3 ^ 40 * 3192260 * 2
def baseEnd_3192260 : Nat := 364258612027063444837571

theorem tailTrace_3192260 : CollatzResearch.WordTrace tailWord_3192260 prefixEnd_3192260 364258612027063444837571 := by
  unfold tailWord_3192260
  simp only [CollatzResearch.WordTrace]
  refine ⟨58215643707497344723975117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77620858276663126298633489 58215643707497344723975117)
  ·
    refine ⟨21830866390311504271490669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58215643707497344723975117 21830866390311504271490669)
    ·
      refine ⟨8186574896366814101809001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21830866390311504271490669 8186574896366814101809001)
      ·
        refine ⟨6139931172275110576356751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8186574896366814101809001 6139931172275110576356751)
        ·
          refine ⟨9209896758412665864535127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6139931172275110576356751 9209896758412665864535127)
          ·
            refine ⟨13814845137618998796802691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9209896758412665864535127 13814845137618998796802691)
            ·
              refine ⟨20722267706428498195204037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13814845137618998796802691 20722267706428498195204037)
              ·
                refine ⟨3885425194955343411600757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20722267706428498195204037 3885425194955343411600757)
                ·
                  refine ⟨364258612027063444837571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3885425194955343411600757 364258612027063444837571)
                  ·
                    rfl

theorem cell22_3192260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_3192260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192260 prefixEnd_3192260 := by exact prefixLift 3192260
  have htrace : WordTrace (prefixWord ++ tailWord_3192260) baseStart_3192260 baseEnd_3192260 := by
    simpa [prefixWord, tailWord_3192260, baseEnd_3192260] using wordTrace_append hprefix tailTrace_3192260
  have hstable : (prefixWord ++ tailWord_3192260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192260).length < 2 ^ (prefixWord ++ tailWord_3192260).sum := by decide
  have hdescent : baseEnd_3192260 < baseStart_3192260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192303 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 1, 5]
def baseStart_3192303 : Nat := 118140960795 + 3192303 * 2 ^ 59
def prefixEnd_3192303 : Nat := 4983230072969 + 3 ^ 40 * 3192303 * 2
def baseEnd_3192303 : Nat := 1092790555859952555687581

theorem tailTrace_3192303 : CollatzResearch.WordTrace tailWord_3192303 prefixEnd_3192303 1092790555859952555687581 := by
  unfold tailWord_3192303
  simp only [CollatzResearch.WordTrace]
  refine ⟨116432855753838907791765563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77621903835892605194510375 116432855753838907791765563)
  ·
    refine ⟨174649283630758361687648345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116432855753838907791765563 174649283630758361687648345)
    ·
      refine ⟨130986962723068771265736259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174649283630758361687648345 130986962723068771265736259)
      ·
        refine ⟨196480444084603156898604389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130986962723068771265736259 196480444084603156898604389)
        ·
          refine ⟨36840083265863091918488323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196480444084603156898604389 36840083265863091918488323)
          ·
            refine ⟨55260124898794637877732485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36840083265863091918488323 55260124898794637877732485)
            ·
              refine ⟨10361273418523994602074841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55260124898794637877732485 10361273418523994602074841)
              ·
                refine ⟨7770955063892995951556131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10361273418523994602074841 7770955063892995951556131)
                ·
                  refine ⟨11656432595839493927334197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770955063892995951556131 11656432595839493927334197)
                  ·
                    refine ⟨1092790555859952555687581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11656432595839493927334197 1092790555859952555687581)
                    ·
                      rfl

theorem cell22_3192303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_3192303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192303 prefixEnd_3192303 := by exact prefixLift 3192303
  have htrace : WordTrace (prefixWord ++ tailWord_3192303) baseStart_3192303 baseEnd_3192303 := by
    simpa [prefixWord, tailWord_3192303, baseEnd_3192303] using wordTrace_append hprefix tailTrace_3192303
  have hstable : (prefixWord ++ tailWord_3192303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192303).length < 2 ^ (prefixWord ++ tailWord_3192303).sum := by decide
  have hdescent : baseEnd_3192303 < baseStart_3192303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192305 : List Nat := [1, 2, 2, 2, 3, 2, 1, 5, 4]
def baseStart_3192305 : Nat := 118140960795 + 3192305 * 2 ^ 59
def prefixEnd_3192305 : Nat := 4983230072969 + 3 ^ 40 * 3192305 * 2
def baseEnd_3192305 : Nat := 364263746833608405712525

theorem tailTrace_3192305 : CollatzResearch.WordTrace tailWord_3192305 prefixEnd_3192305 364263746833608405712525 := by
  unfold tailWord_3192305
  simp only [CollatzResearch.WordTrace]
  refine ⟨116432928699831662133338369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77621952466554441422225579 116432928699831662133338369)
  ·
    refine ⟨87324696524873746600003777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116432928699831662133338369 87324696524873746600003777)
    ·
      refine ⟨65493522393655309950002833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87324696524873746600003777 65493522393655309950002833)
      ·
        refine ⟨49120141795241482462502125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65493522393655309950002833 49120141795241482462502125)
        ·
          refine ⟨18420053173215555923438297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49120141795241482462502125 18420053173215555923438297)
          ·
            refine ⟨13815039879911666942578723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18420053173215555923438297 13815039879911666942578723)
            ·
              refine ⟨20722559819867500413868085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13815039879911666942578723 20722559819867500413868085)
              ·
                refine ⟨1942739983112578163800133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20722559819867500413868085 1942739983112578163800133)
                ·
                  refine ⟨364263746833608405712525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1942739983112578163800133 364263746833608405712525)
                  ·
                    rfl

theorem cell22_3192305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 4].length) (baseStart_3192305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192305 prefixEnd_3192305 := by exact prefixLift 3192305
  have htrace : WordTrace (prefixWord ++ tailWord_3192305) baseStart_3192305 baseEnd_3192305 := by
    simpa [prefixWord, tailWord_3192305, baseEnd_3192305] using wordTrace_append hprefix tailTrace_3192305
  have hstable : (prefixWord ++ tailWord_3192305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192305).length < 2 ^ (prefixWord ++ tailWord_3192305).sum := by decide
  have hdescent : baseEnd_3192305 < baseStart_3192305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192322 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 6]
def baseStart_3192322 : Nat := 118140960795 + 3192322 * 2 ^ 59
def prefixEnd_3192322 : Nat := 4983230072969 + 3 ^ 40 * 3192322 * 2
def baseEnd_3192322 : Nat := 364265686649414279820841

theorem tailTrace_3192322 : CollatzResearch.WordTrace tailWord_3192322 prefixEnd_3192322 364265686649414279820841 := by
  unfold tailWord_3192322
  simp only [CollatzResearch.WordTrace]
  refine ⟨29108387185192518509176805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77622365827180049357804813 29108387185192518509176805)
  ·
    refine ⟨5457822597223597220470651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29108387185192518509176805 5457822597223597220470651)
    ·
      refine ⟨8186733895835395830705977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5457822597223597220470651 8186733895835395830705977)
      ·
        refine ⟨6140050421876546873029483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8186733895835395830705977 6140050421876546873029483)
        ·
          refine ⟨9210075632814820309544225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6140050421876546873029483 9210075632814820309544225)
          ·
            refine ⟨6907556724611115232158169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9210075632814820309544225 6907556724611115232158169)
            ·
              refine ⟨5180667543458336424118627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6907556724611115232158169 5180667543458336424118627)
              ·
                refine ⟨7771001315187504636177941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5180667543458336424118627 7771001315187504636177941)
                ·
                  refine ⟨364265686649414279820841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7771001315187504636177941 364265686649414279820841)
                  ·
                    rfl

theorem cell22_3192322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_3192322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192322 prefixEnd_3192322 := by exact prefixLift 3192322
  have htrace : WordTrace (prefixWord ++ tailWord_3192322) baseStart_3192322 baseEnd_3192322 := by
    simpa [prefixWord, tailWord_3192322, baseEnd_3192322] using wordTrace_append hprefix tailTrace_3192322
  have hstable : (prefixWord ++ tailWord_3192322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192322).length < 2 ^ (prefixWord ++ tailWord_3192322).sum := by decide
  have hdescent : baseEnd_3192322 < baseStart_3192322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192337 : List Nat := [1, 2, 2, 1, 1, 2, 7, 1, 2, 3]
def baseStart_3192337 : Nat := 118140960795 + 3192337 * 2 ^ 59
def prefixEnd_3192337 : Nat := 4983230072969 + 3 ^ 40 * 3192337 * 2
def baseEnd_3192337 : Nat := 1092802194754787800337477

theorem tailTrace_3192337 : CollatzResearch.WordTrace tailWord_3192337 prefixEnd_3192337 1092802194754787800337477 := by
  unfold tailWord_3192337
  simp only [CollatzResearch.WordTrace]
  refine ⟨116434095835715731598503265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77622730557143821065668843 116434095835715731598503265)
  ·
    refine ⟨87325571876786798698877449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116434095835715731598503265 87325571876786798698877449)
    ·
      refine ⟨65494178907590099024158087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87325571876786798698877449 65494178907590099024158087)
      ·
        refine ⟨98241268361385148536237131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65494178907590099024158087 98241268361385148536237131)
        ·
          refine ⟨147361902542077722804355697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98241268361385148536237131 147361902542077722804355697)
          ·
            refine ⟨110521426906558292103266773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147361902542077722804355697 110521426906558292103266773)
            ·
              refine ⟨2590345943122459971170315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 110521426906558292103266773 2590345943122459971170315)
              ·
                refine ⟨3885518914683689956755473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2590345943122459971170315 3885518914683689956755473)
                ·
                  refine ⟨2914139186012767467566605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3885518914683689956755473 2914139186012767467566605)
                  ·
                    refine ⟨1092802194754787800337477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2914139186012767467566605 1092802194754787800337477)
                    ·
                      rfl

theorem cell22_3192337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_3192337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192337 prefixEnd_3192337 := by exact prefixLift 3192337
  have htrace : WordTrace (prefixWord ++ tailWord_3192337) baseStart_3192337 baseEnd_3192337 := by
    simpa [prefixWord, tailWord_3192337, baseEnd_3192337] using wordTrace_append hprefix tailTrace_3192337
  have hstable : (prefixWord ++ tailWord_3192337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192337).length < 2 ^ (prefixWord ++ tailWord_3192337).sum := by decide
  have hdescent : baseEnd_3192337 < baseStart_3192337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192348 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_3192348 : Nat := 118140960795 + 3192348 * 2 ^ 59
def prefixEnd_3192348 : Nat := 4983230072969 + 3 ^ 40 * 3192348 * 2
def baseEnd_3192348 : Nat := 1092805960279587438312443

theorem tailTrace_3192348 : CollatzResearch.WordTrace tailWord_3192348 prefixEnd_3192348 1092805960279587438312443 := by
  unfold tailWord_3192348
  simp only [CollatzResearch.WordTrace]
  refine ⟨58217248519337940238576849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77622998025783920318102465 58217248519337940238576849)
  ·
    refine ⟨43662936389503455178932637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58217248519337940238576849 43662936389503455178932637)
    ·
      refine ⟨16373601146063795692099739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43662936389503455178932637 16373601146063795692099739)
      ·
        refine ⟨24560401719095693538149609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16373601146063795692099739 24560401719095693538149609)
        ·
          refine ⟨18420301289321770153612207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24560401719095693538149609 18420301289321770153612207)
          ·
            refine ⟨27630451933982655230418311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18420301289321770153612207 27630451933982655230418311)
            ·
              refine ⟨41445677900973982845627467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27630451933982655230418311 41445677900973982845627467)
              ·
                refine ⟨62168516851460974268441201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41445677900973982845627467 62168516851460974268441201)
                ·
                  refine ⟨46626387638595730701330901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62168516851460974268441201 46626387638595730701330901)
                  ·
                    refine ⟨1092805960279587438312443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46626387638595730701330901 1092805960279587438312443)
                    ·
                      rfl

theorem cell22_3192348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_3192348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192348 prefixEnd_3192348 := by exact prefixLift 3192348
  have htrace : WordTrace (prefixWord ++ tailWord_3192348) baseStart_3192348 baseEnd_3192348 := by
    simpa [prefixWord, tailWord_3192348, baseEnd_3192348] using wordTrace_append hprefix tailTrace_3192348
  have hstable : (prefixWord ++ tailWord_3192348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192348).length < 2 ^ (prefixWord ++ tailWord_3192348).sum := by decide
  have hdescent : baseEnd_3192348 < baseStart_3192348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192378 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 7]
def baseStart_3192378 : Nat := 118140960795 + 3192378 * 2 ^ 59
def prefixEnd_3192378 : Nat := 4983230072969 + 3 ^ 40 * 3192378 * 2
def baseEnd_3192378 : Nat := 364272076630892453354117

theorem tailTrace_3192378 : CollatzResearch.WordTrace tailWord_3192378 prefixEnd_3192378 364272076630892453354117 := by
  unfold tailWord_3192378
  simp only [CollatzResearch.WordTrace]
  refine ⟨29108897807141798900186447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77623727485711463733830525 29108897807141798900186447)
  ·
    refine ⟨43663346710712698350279671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29108897807141798900186447 43663346710712698350279671)
    ·
      refine ⟨65495020066069047525419507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43663346710712698350279671 65495020066069047525419507)
      ·
        refine ⟨98242530099103571288129261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65495020066069047525419507 98242530099103571288129261)
        ·
          refine ⟨36840948787163839233048473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98242530099103571288129261 36840948787163839233048473)
          ·
            refine ⟨27630711590372879424786355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36840948787163839233048473 27630711590372879424786355)
            ·
              refine ⟨41446067385559319137179533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27630711590372879424786355 41446067385559319137179533)
              ·
                refine ⟨15542275269584744676442325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41446067385559319137179533 15542275269584744676442325)
                ·
                  refine ⟨364272076630892453354117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15542275269584744676442325 364272076630892453354117)
                  ·
                    rfl

theorem cell22_3192378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_3192378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192378 prefixEnd_3192378 := by exact prefixLift 3192378
  have htrace : WordTrace (prefixWord ++ tailWord_3192378) baseStart_3192378 baseEnd_3192378 := by
    simpa [prefixWord, tailWord_3192378, baseEnd_3192378] using wordTrace_append hprefix tailTrace_3192378
  have hstable : (prefixWord ++ tailWord_3192378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192378).length < 2 ^ (prefixWord ++ tailWord_3192378).sum := by decide
  have hdescent : baseEnd_3192378 < baseStart_3192378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192393 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 2, 5]
def baseStart_3192393 : Nat := 118140960795 + 3192393 * 2 ^ 59
def prefixEnd_3192393 : Nat := 4983230072969 + 3 ^ 40 * 3192393 * 2
def baseEnd_3192393 : Nat := 1092821364699222320937305

theorem tailTrace_3192393 : CollatzResearch.WordTrace tailWord_3192393 prefixEnd_3192393 1092821364699222320937305 := by
  unfold tailWord_3192393
  simp only [CollatzResearch.WordTrace]
  refine ⟨116436138323512853162541833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77624092215675235441694555 116436138323512853162541833)
  ·
    refine ⟨87327103742634639871906375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116436138323512853162541833 87327103742634639871906375)
    ·
      refine ⟨130990655613951959807859563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87327103742634639871906375 130990655613951959807859563)
      ·
        refine ⟨196485983420927939711789345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130990655613951959807859563 196485983420927939711789345)
        ·
          refine ⟨147364487565695954783842009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196485983420927939711789345 147364487565695954783842009)
          ·
            refine ⟨110523365674271966087881507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147364487565695954783842009 110523365674271966087881507)
            ·
              refine ⟨165785048511407949131822261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110523365674271966087881507 165785048511407949131822261)
              ·
                refine ⟨15542348297944495231108337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165785048511407949131822261 15542348297944495231108337)
                ·
                  refine ⟨11656761223458371423331253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15542348297944495231108337 11656761223458371423331253)
                  ·
                    refine ⟨1092821364699222320937305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11656761223458371423331253 1092821364699222320937305)
                    ·
                      rfl

theorem cell22_3192393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_3192393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192393 prefixEnd_3192393 := by exact prefixLift 3192393
  have htrace : WordTrace (prefixWord ++ tailWord_3192393) baseStart_3192393 baseEnd_3192393 := by
    simpa [prefixWord, tailWord_3192393, baseEnd_3192393] using wordTrace_append hprefix tailTrace_3192393
  have hstable : (prefixWord ++ tailWord_3192393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192393).length < 2 ^ (prefixWord ++ tailWord_3192393).sum := by decide
  have hdescent : baseEnd_3192393 < baseStart_3192393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192425 : List Nat := [1, 2, 1, 1, 1, 4, 2, 5, 1, 4]
def baseStart_3192425 : Nat := 118140960795 + 3192425 * 2 ^ 59
def prefixEnd_3192425 : Nat := 4983230072969 + 3 ^ 40 * 3192425 * 2
def baseEnd_3192425 : Nat := 1092832318953184904137207

theorem tailTrace_3192425 : CollatzResearch.WordTrace tailWord_3192425 prefixEnd_3192425 1092832318953184904137207 := by
  unfold tailWord_3192425
  simp only [CollatzResearch.WordTrace]
  refine ⟨116437305459396922627706729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77624870306264615085137819 116437305459396922627706729)
  ·
    refine ⟨87327979094547691970780047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116437305459396922627706729 87327979094547691970780047)
    ·
      refine ⟨130991968641821537956170071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87327979094547691970780047 130991968641821537956170071)
      ·
        refine ⟨196487952962732306934255107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130991968641821537956170071 196487952962732306934255107)
        ·
          refine ⟨294731929444098460401382661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196487952962732306934255107 294731929444098460401382661)
          ·
            refine ⟨55262236770768461325259249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294731929444098460401382661 55262236770768461325259249)
            ·
              refine ⟨41446677578076345993944437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55262236770768461325259249 41446677578076345993944437)
              ·
                refine ⟨3885626022944657436932291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41446677578076345993944437 3885626022944657436932291)
                ·
                  refine ⟨5828439034416986155398437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885626022944657436932291 5828439034416986155398437)
                  ·
                    refine ⟨1092832318953184904137207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5828439034416986155398437 1092832318953184904137207)
                    ·
                      rfl

theorem cell22_3192425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_3192425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192425 prefixEnd_3192425 := by exact prefixLift 3192425
  have htrace : WordTrace (prefixWord ++ tailWord_3192425) baseStart_3192425 baseEnd_3192425 := by
    simpa [prefixWord, tailWord_3192425, baseEnd_3192425] using wordTrace_append hprefix tailTrace_3192425
  have hstable : (prefixWord ++ tailWord_3192425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192425).length < 2 ^ (prefixWord ++ tailWord_3192425).sum := by decide
  have hdescent : baseEnd_3192425 < baseStart_3192425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192455 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 1, 5]
def baseStart_3192455 : Nat := 118140960795 + 3192455 * 2 ^ 59
def prefixEnd_3192455 : Nat := 4983230072969 + 3 ^ 40 * 3192455 * 2
def baseEnd_3192455 : Nat := 1092842588566274825887115

theorem tailTrace_3192455 : CollatzResearch.WordTrace tailWord_3192455 prefixEnd_3192455 1092842588566274825887115 := by
  unfold tailWord_3192455
  simp only [CollatzResearch.WordTrace]
  refine ⟨116438399649288237751298819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77625599766192158500865879 116438399649288237751298819)
  ·
    refine ⟨174657599473932356626948229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116438399649288237751298819 174657599473932356626948229)
    ·
      refine ⟨32748299901362316867552793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174657599473932356626948229 32748299901362316867552793)
      ·
        refine ⟨24561224926021737650664595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32748299901362316867552793 24561224926021737650664595)
        ·
          refine ⟨36841837389032606475996893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24561224926021737650664595 36841837389032606475996893)
          ·
            refine ⟨13815689020887227428498835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36841837389032606475996893 13815689020887227428498835)
            ·
              refine ⟨20723533531330841142748253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13815689020887227428498835 20723533531330841142748253)
              ·
                refine ⟨7771325074249065428530595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20723533531330841142748253 7771325074249065428530595)
                ·
                  refine ⟨11656987611373598142795893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7771325074249065428530595 11656987611373598142795893)
                  ·
                    refine ⟨1092842588566274825887115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11656987611373598142795893 1092842588566274825887115)
                    ·
                      rfl

theorem cell22_3192455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_3192455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192455 prefixEnd_3192455 := by exact prefixLift 3192455
  have htrace : WordTrace (prefixWord ++ tailWord_3192455) baseStart_3192455 baseEnd_3192455 := by
    simpa [prefixWord, tailWord_3192455, baseEnd_3192455] using wordTrace_append hprefix tailTrace_3192455
  have hstable : (prefixWord ++ tailWord_3192455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192455).length < 2 ^ (prefixWord ++ tailWord_3192455).sum := by decide
  have hdescent : baseEnd_3192455 < baseStart_3192455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192476 : List Nat := [2, 2, 3, 2, 3, 2, 2, 1, 1, 4]
def baseStart_3192476 : Nat := 118140960795 + 3192476 * 2 ^ 59
def prefixEnd_3192476 : Nat := 4983230072969 + 3 ^ 40 * 3192476 * 2
def baseEnd_3192476 : Nat := 1092849777295437771112051

theorem tailTrace_3192476 : CollatzResearch.WordTrace tailWord_3192476 prefixEnd_3192476 1092849777295437771112051 := by
  unfold tailWord_3192476
  simp only [CollatzResearch.WordTrace]
  refine ⟨58219582791106079168906641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77626110388141438891875521 58219582791106079168906641)
  ·
    refine ⟨43664687093329559376679981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58219582791106079168906641 43664687093329559376679981)
    ·
      refine ⟨16374257659998584766254993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43664687093329559376679981 16374257659998584766254993)
      ·
        refine ⟨12280693244998938574691245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16374257659998584766254993 12280693244998938574691245)
        ·
          refine ⟨4605259966874601965509217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12280693244998938574691245 4605259966874601965509217)
          ·
            refine ⟨3453944975155951474131913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4605259966874601965509217 3453944975155951474131913)
            ·
              refine ⟨2590458731366963605598935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3453944975155951474131913 2590458731366963605598935)
              ·
                refine ⟨3885688097050445408398403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2590458731366963605598935 3885688097050445408398403)
                ·
                  refine ⟨5828532145575668112597605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885688097050445408398403 5828532145575668112597605)
                  ·
                    refine ⟨1092849777295437771112051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5828532145575668112597605 1092849777295437771112051)
                    ·
                      rfl

theorem cell22_3192476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_3192476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192476 prefixEnd_3192476 := by exact prefixLift 3192476
  have htrace : WordTrace (prefixWord ++ tailWord_3192476) baseStart_3192476 baseEnd_3192476 := by
    simpa [prefixWord, tailWord_3192476, baseEnd_3192476] using wordTrace_append hprefix tailTrace_3192476
  have hstable : (prefixWord ++ tailWord_3192476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192476).length < 2 ^ (prefixWord ++ tailWord_3192476).sum := by decide
  have hdescent : baseEnd_3192476 < baseStart_3192476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192575 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 6]
def baseStart_3192575 : Nat := 118140960795 + 3192575 * 2 ^ 59
def prefixEnd_3192575 : Nat := 4983230072969 + 3 ^ 40 * 3192575 * 2
def baseEnd_3192575 : Nat := 364294555672878170962249

theorem tailTrace_3192575 : CollatzResearch.WordTrace tailWord_3192575 prefixEnd_3192575 364294555672878170962249 := by
  unfold tailWord_3192575
  simp only [CollatzResearch.WordTrace]
  refine ⟨116442776408853498245667179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77628517605902332163778119 116442776408853498245667179)
  ·
    refine ⟨174664164613280247368500769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116442776408853498245667179 174664164613280247368500769)
    ·
      refine ⟨130998123459960185526375577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174664164613280247368500769 130998123459960185526375577)
      ·
        refine ⟨98248592594970139144781683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130998123459960185526375577 98248592594970139144781683)
        ·
          refine ⟨147372888892455208717172525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98248592594970139144781683 147372888892455208717172525)
          ·
            refine ⟨55264833334670703268939697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147372888892455208717172525 55264833334670703268939697)
            ·
              refine ⟨41448625001003027451704773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55264833334670703268939697 41448625001003027451704773)
              ·
                refine ⟨7771617187688067647194645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41448625001003027451704773 7771617187688067647194645)
                ·
                  refine ⟨364294555672878170962249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7771617187688067647194645 364294555672878170962249)
                  ·
                    rfl

theorem cell22_3192575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 6].length) (baseStart_3192575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192575 prefixEnd_3192575 := by exact prefixLift 3192575
  have htrace : WordTrace (prefixWord ++ tailWord_3192575) baseStart_3192575 baseEnd_3192575 := by
    simpa [prefixWord, tailWord_3192575, baseEnd_3192575] using wordTrace_append hprefix tailTrace_3192575
  have hstable : (prefixWord ++ tailWord_3192575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192575).length < 2 ^ (prefixWord ++ tailWord_3192575).sum := by decide
  have hdescent : baseEnd_3192575 < baseStart_3192575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192609 : List Nat := [1, 2, 3, 2, 1, 4, 1, 4, 4]
def baseStart_3192609 : Nat := 118140960795 + 3192609 * 2 ^ 59
def prefixEnd_3192609 : Nat := 4983230072969 + 3 ^ 40 * 3192609 * 2
def baseEnd_3192609 : Nat := 364298435304489919178881

theorem tailTrace_3192609 : CollatzResearch.WordTrace tailWord_3192609 prefixEnd_3192609 364298435304489919178881 := by
  unfold tailWord_3192609
  simp only [CollatzResearch.WordTrace]
  refine ⟨116444016490730322052404881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77629344327153548034936587 116444016490730322052404881)
  ·
    refine ⟨87333012368047741539303661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116444016490730322052404881 87333012368047741539303661)
    ·
      refine ⟨32749879638017903077238873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87333012368047741539303661 32749879638017903077238873)
      ·
        refine ⟨24562409728513427307929155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32749879638017903077238873 24562409728513427307929155)
        ·
          refine ⟨36843614592770140961893733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24562409728513427307929155 36843614592770140961893733)
          ·
            refine ⟨6908177736144401430355075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36843614592770140961893733 6908177736144401430355075)
            ·
              refine ⟨10362266604216602145532613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6908177736144401430355075 10362266604216602145532613)
              ·
                refine ⟨1942924988290612902287365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10362266604216602145532613 1942924988290612902287365)
                ·
                  refine ⟨364298435304489919178881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1942924988290612902287365 364298435304489919178881)
                  ·
                    rfl

theorem cell22_3192609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 4].length) (baseStart_3192609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192609 prefixEnd_3192609 := by exact prefixLift 3192609
  have htrace : WordTrace (prefixWord ++ tailWord_3192609) baseStart_3192609 baseEnd_3192609 := by
    simpa [prefixWord, tailWord_3192609, baseEnd_3192609] using wordTrace_append hprefix tailTrace_3192609
  have hstable : (prefixWord ++ tailWord_3192609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192609).length < 2 ^ (prefixWord ++ tailWord_3192609).sum := by decide
  have hdescent : baseEnd_3192609 < baseStart_3192609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192686 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_3192686 : Nat := 118140960795 + 3192686 * 2 ^ 59
def prefixEnd_3192686 : Nat := 4983230072969 + 3 ^ 40 * 3192686 * 2
def baseEnd_3192686 : Nat := 1092921664587067223361407

theorem tailTrace_3192686 : CollatzResearch.WordTrace tailWord_3192686 prefixEnd_3192686 1092921664587067223361407 := by
  unfold tailWord_3192686
  simp only [CollatzResearch.WordTrace]
  refine ⟨14555853113931420525369739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77631216607634242801971941 14555853113931420525369739)
  ·
    refine ⟨21833779670897130788054609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14555853113931420525369739 21833779670897130788054609)
    ·
      refine ⟨16375334753172848091040957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21833779670897130788054609 16375334753172848091040957)
      ·
        refine ⟨6140750532439818034140359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16375334753172848091040957 6140750532439818034140359)
        ·
          refine ⟨9211125798659727051210539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6140750532439818034140359 9211125798659727051210539)
          ·
            refine ⟨13816688697989590576815809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9211125798659727051210539 13816688697989590576815809)
            ·
              refine ⟨10362516523492192932611857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13816688697989590576815809 10362516523492192932611857)
              ·
                refine ⟨7771887392619144699458893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10362516523492192932611857 7771887392619144699458893)
                ·
                  refine ⟨2914457772232179262297085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7771887392619144699458893 2914457772232179262297085)
                  ·
                    refine ⟨1092921664587067223361407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2914457772232179262297085 1092921664587067223361407)
                    ·
                      rfl

theorem cell22_3192686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_3192686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192686 prefixEnd_3192686 := by exact prefixLift 3192686
  have htrace : WordTrace (prefixWord ++ tailWord_3192686) baseStart_3192686 baseEnd_3192686 := by
    simpa [prefixWord, tailWord_3192686, baseEnd_3192686] using wordTrace_append hprefix tailTrace_3192686
  have hstable : (prefixWord ++ tailWord_3192686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192686).length < 2 ^ (prefixWord ++ tailWord_3192686).sum := by decide
  have hdescent : baseEnd_3192686 < baseStart_3192686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192772 : List Nat := [2, 3, 3, 14]
def baseStart_3192772 : Nat := 118140960795 + 3192772 * 2 ^ 59
def prefixEnd_3192772 : Nat := 4983230072969 + 3 ^ 40 * 3192772 * 2
def baseEnd_3192772 : Nat := 1499247056439769088767

theorem tailTrace_3192772 : CollatzResearch.WordTrace tailWord_3192772 prefixEnd_3192772 1499247056439769088767 := by
  unfold tailWord_3192772
  simp only [CollatzResearch.WordTrace]
  refine ⟨58224980794569900445294285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77633307726093200593725713 58224980794569900445294285)
  ·
    refine ⟨21834367797963712666985357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58224980794569900445294285 21834367797963712666985357)
    ·
      refine ⟨8187887924236392250119509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21834367797963712666985357 8187887924236392250119509)
      ·
        refine ⟨1499247056439769088767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 8187887924236392250119509 1499247056439769088767)
        ·
          rfl

theorem cell22_3192772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 14].length) (baseStart_3192772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192772 prefixEnd_3192772 := by exact prefixLift 3192772
  have htrace : WordTrace (prefixWord ++ tailWord_3192772) baseStart_3192772 baseEnd_3192772 := by
    simpa [prefixWord, tailWord_3192772, baseEnd_3192772] using wordTrace_append hprefix tailTrace_3192772
  have hstable : (prefixWord ++ tailWord_3192772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192772).length < 2 ^ (prefixWord ++ tailWord_3192772).sum := by decide
  have hdescent : baseEnd_3192772 < baseStart_3192772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192776 : List Nat := [2, 1, 3, 1, 4, 1, 1, 4, 2, 3]
def baseStart_3192776 : Nat := 118140960795 + 3192776 * 2 ^ 59
def prefixEnd_3192776 : Nat := 4983230072969 + 3 ^ 40 * 3192776 * 2
def baseEnd_3192776 : Nat := 1092952473426336988611131

theorem tailTrace_3192776 : CollatzResearch.WordTrace tailWord_3192776 prefixEnd_3192776 1092952473426336988611131 := by
  unfold tailWord_3192776
  simp only [CollatzResearch.WordTrace]
  refine ⟨58225053740562654786867091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77633404987416873049156121 58225053740562654786867091)
  ·
    refine ⟨87337580610843982180300637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58225053740562654786867091 87337580610843982180300637)
    ·
      refine ⟨32751592729066493317612739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87337580610843982180300637 32751592729066493317612739)
      ·
        refine ⟨49127389093599739976419109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32751592729066493317612739 49127389093599739976419109)
        ·
          refine ⟨9211385455049951245578583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49127389093599739976419109 9211385455049951245578583)
          ·
            refine ⟨13817078182574926868367875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9211385455049951245578583 13817078182574926868367875)
            ·
              refine ⟨20725617273862390302551813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13817078182574926868367875 20725617273862390302551813)
              ·
                refine ⟨3886053238849198181728465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20725617273862390302551813 3886053238849198181728465)
                ·
                  refine ⟨2914539929136898636296349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3886053238849198181728465 2914539929136898636296349)
                  ·
                    refine ⟨1092952473426336988611131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2914539929136898636296349 1092952473426336988611131)
                    ·
                      rfl

theorem cell22_3192776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_3192776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192776 prefixEnd_3192776 := by exact prefixLift 3192776
  have htrace : WordTrace (prefixWord ++ tailWord_3192776) baseStart_3192776 baseEnd_3192776 := by
    simpa [prefixWord, tailWord_3192776, baseEnd_3192776] using wordTrace_append hprefix tailTrace_3192776
  have hstable : (prefixWord ++ tailWord_3192776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192776).length < 2 ^ (prefixWord ++ tailWord_3192776).sum := by decide
  have hdescent : baseEnd_3192776 < baseStart_3192776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192789 : List Nat := [1, 3, 2, 3, 2, 1, 3, 7]
def baseStart_3192789 : Nat := 118140960795 + 3192789 * 2 ^ 59
def prefixEnd_3192789 : Nat := 4983230072969 + 3 ^ 40 * 3192789 * 2
def baseEnd_3192789 : Nat := 121439658176889920892899

theorem tailTrace_3192789 : CollatzResearch.WordTrace tailWord_3192789 prefixEnd_3192789 121439658176889920892899 := by
  unfold tailWord_3192789
  simp only [CollatzResearch.WordTrace]
  refine ⟨116450581630078212793957421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77633721086718808529304947 116450581630078212793957421)
  ·
    refine ⟨43668968111279329797734033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116450581630078212793957421 43668968111279329797734033)
    ·
      refine ⟨32751726083459497348300525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43668968111279329797734033 32751726083459497348300525)
      ·
        refine ⟨12281897281297311505612697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32751726083459497348300525 12281897281297311505612697)
        ·
          refine ⟨9211422960972983629209523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12281897281297311505612697 9211422960972983629209523)
          ·
            refine ⟨13817134441459475443814285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9211422960972983629209523 13817134441459475443814285)
            ·
              refine ⟨5181425415547303291430357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13817134441459475443814285 5181425415547303291430357)
              ·
                refine ⟨121439658176889920892899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5181425415547303291430357 121439658176889920892899)
                ·
                  rfl

theorem cell22_3192789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 7].length) (baseStart_3192789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192789 prefixEnd_3192789 := by exact prefixLift 3192789
  have htrace : WordTrace (prefixWord ++ tailWord_3192789) baseStart_3192789 baseEnd_3192789 := by
    simpa [prefixWord, tailWord_3192789, baseEnd_3192789] using wordTrace_append hprefix tailTrace_3192789
  have hstable : (prefixWord ++ tailWord_3192789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192789).length < 2 ^ (prefixWord ++ tailWord_3192789).sum := by decide
  have hdescent : baseEnd_3192789 < baseStart_3192789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192881 : List Nat := [1, 2, 2, 3, 1, 3, 2, 3, 1, 4]
def baseStart_3192881 : Nat := 118140960795 + 3192881 * 2 ^ 59
def prefixEnd_3192881 : Nat := 4983230072969 + 3 ^ 40 * 3192881 * 2
def baseEnd_3192881 : Nat := 1092988417072151714735809

theorem tailTrace_3192881 : CollatzResearch.WordTrace tailWord_3192881 prefixEnd_3192881 1092988417072151714735809 := by
  unfold tailWord_3192881
  simp only [CollatzResearch.WordTrace]
  refine ⟨116453937145744912506306497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77635958097163275004204331 116453937145744912506306497)
  ·
    refine ⟨87340452859308684379729873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116453937145744912506306497 87340452859308684379729873)
    ·
      refine ⟨65505339644481513284797405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87340452859308684379729873 65505339644481513284797405)
      ·
        refine ⟨24564502366680567481799027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65505339644481513284797405 24564502366680567481799027)
        ·
          refine ⟨36846753550020851222698541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24564502366680567481799027 36846753550020851222698541)
          ·
            refine ⟨13817532581257819208511953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36846753550020851222698541 13817532581257819208511953)
            ·
              refine ⟨10363149435943364406383965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13817532581257819208511953 10363149435943364406383965)
              ·
                refine ⟨3886181038478761652393987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10363149435943364406383965 3886181038478761652393987)
                ·
                  refine ⟨5829271557718142478590981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3886181038478761652393987 5829271557718142478590981)
                  ·
                    refine ⟨1092988417072151714735809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5829271557718142478590981 1092988417072151714735809)
                    ·
                      rfl

theorem cell22_3192881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_3192881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192881 prefixEnd_3192881 := by exact prefixLift 3192881
  have htrace : WordTrace (prefixWord ++ tailWord_3192881) baseStart_3192881 baseEnd_3192881 := by
    simpa [prefixWord, tailWord_3192881, baseEnd_3192881] using wordTrace_append hprefix tailTrace_3192881
  have hstable : (prefixWord ++ tailWord_3192881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192881).length < 2 ^ (prefixWord ++ tailWord_3192881).sum := by decide
  have hdescent : baseEnd_3192881 < baseStart_3192881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192896 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 6]
def baseStart_3192896 : Nat := 118140960795 + 3192896 * 2 ^ 59
def prefixEnd_3192896 : Nat := 4983230072969 + 3 ^ 40 * 3192896 * 2
def baseEnd_3192896 : Nat := 364331183959565558536921

theorem tailTrace_3192896 : CollatzResearch.WordTrace tailWord_3192896 prefixEnd_3192896 364331183959565558536921 := by
  unfold tailWord_3192896
  simp only [CollatzResearch.WordTrace]
  refine ⟨58227242120345285034051271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77636322827127046712068361 58227242120345285034051271)
  ·
    refine ⟨87340863180517927551076907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58227242120345285034051271 87340863180517927551076907)
    ·
      refine ⟨131011294770776891326615361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87340863180517927551076907 131011294770776891326615361)
      ·
        refine ⟨98258471078082668494961521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131011294770776891326615361 98258471078082668494961521)
        ·
          refine ⟨73693853308562001371221141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98258471078082668494961521 73693853308562001371221141)
          ·
            refine ⟨3454399373838843814275991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73693853308562001371221141 3454399373838843814275991)
            ·
              refine ⟨5181599060758265721413987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3454399373838843814275991 5181599060758265721413987)
              ·
                refine ⟨7772398591137398582120981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5181599060758265721413987 7772398591137398582120981)
                ·
                  refine ⟨364331183959565558536921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7772398591137398582120981 364331183959565558536921)
                  ·
                    rfl

theorem cell22_3192896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 6].length) (baseStart_3192896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192896 prefixEnd_3192896 := by exact prefixLift 3192896
  have htrace : WordTrace (prefixWord ++ tailWord_3192896) baseStart_3192896 baseEnd_3192896 := by
    simpa [prefixWord, tailWord_3192896, baseEnd_3192896] using wordTrace_append hprefix tailTrace_3192896
  have hstable : (prefixWord ++ tailWord_3192896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192896).length < 2 ^ (prefixWord ++ tailWord_3192896).sum := by decide
  have hdescent : baseEnd_3192896 < baseStart_3192896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192911 : List Nat := [1, 1, 2, 1, 1, 2, 2, 7, 2, 3]
def baseStart_3192911 : Nat := 118140960795 + 3192911 * 2 ^ 59
def prefixEnd_3192911 : Nat := 4983230072969 + 3 ^ 40 * 3192911 * 2
def baseEnd_3192911 : Nat := 1092998686685241636485717

theorem tailTrace_3192911 : CollatzResearch.WordTrace tailWord_3192911 prefixEnd_3192911 1092998686685241636485717 := by
  unfold tailWord_3192911
  simp only [CollatzResearch.WordTrace]
  refine ⟨116455031335636227629898587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77636687557090818419932391 116455031335636227629898587)
  ·
    refine ⟨174682547003454341444847881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116455031335636227629898587 174682547003454341444847881)
    ·
      refine ⟨131011910252590756083635911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174682547003454341444847881 131011910252590756083635911)
      ·
        refine ⟨196517865378886134125453867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131011910252590756083635911 196517865378886134125453867)
        ·
          refine ⟨294776798068329201188180801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196517865378886134125453867 294776798068329201188180801)
          ·
            refine ⟨221082598551246900891135601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294776798068329201188180801 221082598551246900891135601)
            ·
              refine ⟨165811948913435175668351701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221082598551246900891135601 165811948913435175668351701)
              ·
                refine ⟨3886217552658636929726993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 165811948913435175668351701 3886217552658636929726993)
                ·
                  refine ⟨2914663164493977697295245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3886217552658636929726993 2914663164493977697295245)
                  ·
                    refine ⟨1092998686685241636485717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2914663164493977697295245 1092998686685241636485717)
                    ·
                      rfl

theorem cell22_3192911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 3].length) (baseStart_3192911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3192911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3192911 prefixEnd_3192911 := by exact prefixLift 3192911
  have htrace : WordTrace (prefixWord ++ tailWord_3192911) baseStart_3192911 baseEnd_3192911 := by
    simpa [prefixWord, tailWord_3192911, baseEnd_3192911] using wordTrace_append hprefix tailTrace_3192911
  have hstable : (prefixWord ++ tailWord_3192911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192911).length < 2 ^ (prefixWord ++ tailWord_3192911).sum := by decide
  have hdescent : baseEnd_3192911 < baseStart_3192911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193020 : List Nat := [2, 2, 2, 3, 3, 1, 3, 1, 5]
def baseStart_3193020 : Nat := 118140960795 + 3193020 * 2 ^ 59
def prefixEnd_3193020 : Nat := 4983230072969 + 3 ^ 40 * 3193020 * 2
def baseEnd_3193020 : Nat := 364345333204267228503461

theorem tailTrace_3193020 : CollatzResearch.WordTrace tailWord_3193020 prefixEnd_3193020 364345333204267228503461 := by
  unfold tailWord_3193020
  simp only [CollatzResearch.WordTrace]
  refine ⟨58229503446120669622808257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77639337928160892830411009 58229503446120669622808257)
  ·
    refine ⟨43672127584590502217106193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58229503446120669622808257 43672127584590502217106193)
    ·
      refine ⟨32754095688442876662829645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43672127584590502217106193 32754095688442876662829645)
      ·
        refine ⟨12282785883166078748561117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32754095688442876662829645 12282785883166078748561117)
        ·
          refine ⟨4606044706187279530710419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12282785883166078748561117 4606044706187279530710419)
          ·
            refine ⟨6909067059280919296065629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4606044706187279530710419 6909067059280919296065629)
            ·
              refine ⟨2590900147230344736024611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6909067059280919296065629 2590900147230344736024611)
              ·
                refine ⟨3886350220845517104036917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2590900147230344736024611 3886350220845517104036917)
                ·
                  refine ⟨364345333204267228503461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3886350220845517104036917 364345333204267228503461)
                  ·
                    rfl

theorem cell22_3193020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_3193020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193020 prefixEnd_3193020 := by exact prefixLift 3193020
  have htrace : WordTrace (prefixWord ++ tailWord_3193020) baseStart_3193020 baseEnd_3193020 := by
    simpa [prefixWord, tailWord_3193020, baseEnd_3193020] using wordTrace_append hprefix tailTrace_3193020
  have hstable : (prefixWord ++ tailWord_3193020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193020).length < 2 ^ (prefixWord ++ tailWord_3193020).sum := by decide
  have hdescent : baseEnd_3193020 < baseStart_3193020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193058 : List Nat := [3, 3, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3193058 : Nat := 118140960795 + 3193058 * 2 ^ 59
def prefixEnd_3193058 : Nat := 4983230072969 + 3 ^ 40 * 3193058 * 2
def baseEnd_3193058 : Nat := 1093049007789382253060267

theorem tailTrace_3193058 : CollatzResearch.WordTrace tailWord_3193058 prefixEnd_3193058 1093049007789382253060267 := by
  unfold tailWord_3193058
  simp only [CollatzResearch.WordTrace]
  refine ⟨29115098216525917933874957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77640261910735781156999885 29115098216525917933874957)
  ·
    refine ⟨10918161831197219225203109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29115098216525917933874957 10918161831197219225203109)
    ·
      refine ⟨2047155343349478604725583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10918161831197219225203109 2047155343349478604725583)
      ·
        refine ⟨3070733015024217907088375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2047155343349478604725583 3070733015024217907088375)
        ·
          refine ⟨4606099522536326860632563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3070733015024217907088375 4606099522536326860632563)
          ·
            refine ⟨6909149283804490290948845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4606099522536326860632563 6909149283804490290948845)
            ·
              refine ⟨2590930981426683859105817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6909149283804490290948845 2590930981426683859105817)
              ·
                refine ⟨1943198236070012894329363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2590930981426683859105817 1943198236070012894329363)
                ·
                  refine ⟨2914797354105019341494045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943198236070012894329363 2914797354105019341494045)
                  ·
                    refine ⟨1093049007789382253060267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2914797354105019341494045 1093049007789382253060267)
                    ·
                      rfl

theorem cell22_3193058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3193058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193058 prefixEnd_3193058 := by exact prefixLift 3193058
  have htrace : WordTrace (prefixWord ++ tailWord_3193058) baseStart_3193058 baseEnd_3193058 := by
    simpa [prefixWord, tailWord_3193058, baseEnd_3193058] using wordTrace_append hprefix tailTrace_3193058
  have hstable : (prefixWord ++ tailWord_3193058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193058).length < 2 ^ (prefixWord ++ tailWord_3193058).sum := by decide
  have hdescent : baseEnd_3193058 < baseStart_3193058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193121 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 7]
def baseStart_3193121 : Nat := 118140960795 + 3193121 * 2 ^ 59
def prefixEnd_3193121 : Nat := 4983230072969 + 3 ^ 40 * 3193121 * 2
def baseEnd_3193121 : Nat := 364356857992290362911691

theorem tailTrace_3193121 : CollatzResearch.WordTrace tailWord_3193121 prefixEnd_3193121 364356857992290362911691 := by
  unfold tailWord_3193121
  simp only [CollatzResearch.WordTrace]
  refine ⟨116462690664875433495043217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77641793776583622330028811 116462690664875433495043217)
  ·
    refine ⟨87347017998656575121282413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116462690664875433495043217 87347017998656575121282413)
    ·
      refine ⟨32755131749496215670480905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87347017998656575121282413 32755131749496215670480905)
      ·
        refine ⟨24566348812122161752860679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32755131749496215670480905 24566348812122161752860679)
        ·
          refine ⟨36849523218183242629291019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24566348812122161752860679 36849523218183242629291019)
          ·
            refine ⟨55274284827274863943936529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36849523218183242629291019 55274284827274863943936529)
            ·
              refine ⟨41455713620456147957952397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55274284827274863943936529 41455713620456147957952397)
              ·
                refine ⟨15545892607671055484232149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41455713620456147957952397 15545892607671055484232149)
                ·
                  refine ⟨364356857992290362911691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15545892607671055484232149 364356857992290362911691)
                  ·
                    rfl

theorem cell22_3193121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_3193121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193121 prefixEnd_3193121 := by exact prefixLift 3193121
  have htrace : WordTrace (prefixWord ++ tailWord_3193121) baseStart_3193121 baseEnd_3193121 := by
    simpa [prefixWord, tailWord_3193121, baseEnd_3193121] using wordTrace_append hprefix tailTrace_3193121
  have hstable : (prefixWord ++ tailWord_3193121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193121).length < 2 ^ (prefixWord ++ tailWord_3193121).sum := by decide
  have hdescent : baseEnd_3193121 < baseStart_3193121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193213 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_3193213 : Nat := 118140960795 + 3193213 * 2 ^ 59
def prefixEnd_3193213 : Nat := 4983230072969 + 3 ^ 40 * 3193213 * 2
def baseEnd_3193213 : Nat := 1093102067457013515434791

theorem tailTrace_3193213 : CollatzResearch.WordTrace tailWord_3193213 prefixEnd_3193213 1093102067457013515434791 := by
  unfold tailWord_3193213
  simp only [CollatzResearch.WordTrace]
  refine ⟨116466046180542133207392293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77644030787028088804928195 116466046180542133207392293)
  ·
    refine ⟨21837383658851649976386055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116466046180542133207392293 21837383658851649976386055)
    ·
      refine ⟨32756075488277474964579083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21837383658851649976386055 32756075488277474964579083)
      ·
        refine ⟨49134113232416212446868625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32756075488277474964579083 49134113232416212446868625)
        ·
          refine ⟨36850584924312159335151469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49134113232416212446868625 36850584924312159335151469)
          ·
            refine ⟨13818969346617059750681801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36850584924312159335151469 13818969346617059750681801)
            ·
              refine ⟨10364227009962794813011351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13818969346617059750681801 10364227009962794813011351)
              ·
                refine ⟨15546340514944192219517027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10364227009962794813011351 15546340514944192219517027)
                ·
                  refine ⟨23319510772416288329275541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15546340514944192219517027 23319510772416288329275541)
                  ·
                    refine ⟨1093102067457013515434791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23319510772416288329275541 1093102067457013515434791)
                    ·
                      rfl

theorem cell22_3193213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_3193213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193213 prefixEnd_3193213 := by exact prefixLift 3193213
  have htrace : WordTrace (prefixWord ++ tailWord_3193213) baseStart_3193213 baseEnd_3193213 := by
    simpa [prefixWord, tailWord_3193213, baseEnd_3193213] using wordTrace_append hprefix tailTrace_3193213
  have hstable : (prefixWord ++ tailWord_3193213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193213).length < 2 ^ (prefixWord ++ tailWord_3193213).sum := by decide
  have hdescent : baseEnd_3193213 < baseStart_3193213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193217 : List Nat := [1, 2, 4, 3, 1, 1, 3, 3, 4]
def baseStart_3193217 : Nat := 118140960795 + 3193217 * 2 ^ 59
def prefixEnd_3193217 : Nat := 4983230072969 + 3 ^ 40 * 3193217 * 2
def baseEnd_3193217 : Nat := 364367812246252946111593

theorem tailTrace_3193217 : CollatzResearch.WordTrace tailWord_3193217 prefixEnd_3193217 364367812246252946111593 := by
  unfold tailWord_3193217
  simp only [CollatzResearch.WordTrace]
  refine ⟨116466192072527641890537905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77644128048351761260358603 116466192072527641890537905)
  ·
    refine ⟨87349644054395731417903429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116466192072527641890537905 87349644054395731417903429)
    ·
      refine ⟨16378058260199199640856893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87349644054395731417903429 16378058260199199640856893)
      ·
        refine ⟨6141771847574699865321335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16378058260199199640856893 6141771847574699865321335)
        ·
          refine ⟨9212657771362049797982003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6141771847574699865321335 9212657771362049797982003)
          ·
            refine ⟨13818986657043074696973005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9212657771362049797982003 13818986657043074696973005)
            ·
              refine ⟨5182119996391153011364877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13818986657043074696973005 5182119996391153011364877)
              ·
                refine ⟨1943294998646682379261829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5182119996391153011364877 1943294998646682379261829)
                ·
                  refine ⟨364367812246252946111593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1943294998646682379261829 364367812246252946111593)
                  ·
                    rfl

theorem cell22_3193217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 4].length) (baseStart_3193217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193217 prefixEnd_3193217 := by exact prefixLift 3193217
  have htrace : WordTrace (prefixWord ++ tailWord_3193217) baseStart_3193217 baseEnd_3193217 := by
    simpa [prefixWord, tailWord_3193217, baseEnd_3193217] using wordTrace_append hprefix tailTrace_3193217
  have hstable : (prefixWord ++ tailWord_3193217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193217).length < 2 ^ (prefixWord ++ tailWord_3193217).sum := by decide
  have hdescent : baseEnd_3193217 < baseStart_3193217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193228 : List Nat := [2, 2, 1, 2, 1, 6, 8]
def baseStart_3193228 : Nat := 118140960795 + 3193228 * 2 ^ 59
def prefixEnd_3193228 : Nat := 4983230072969 + 3 ^ 40 * 3193228 * 2
def baseEnd_3193228 : Nat := 40485451935687350974435

theorem tailTrace_3193228 : CollatzResearch.WordTrace tailWord_3193228 prefixEnd_3193228 40485451935687350974435 := by
  unfold tailWord_3193228
  simp only [CollatzResearch.WordTrace]
  refine ⟨58233296637743895384594169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77644395516991860512792225 58233296637743895384594169)
  ·
    refine ⟨43674972478307921538445627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58233296637743895384594169 43674972478307921538445627)
    ·
      refine ⟨65512458717461882307668441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43674972478307921538445627 65512458717461882307668441)
      ·
        refine ⟨49134344038096411730751331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65512458717461882307668441 49134344038096411730751331)
        ·
          refine ⟨73701516057144617596126997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49134344038096411730751331 73701516057144617596126997)
          ·
            refine ⟨3454758565178653949818453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73701516057144617596126997 3454758565178653949818453)
            ·
              refine ⟨40485451935687350974435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3454758565178653949818453 40485451935687350974435)
              ·
                rfl

theorem cell22_3193228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 8].length) (baseStart_3193228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193228 prefixEnd_3193228 := by exact prefixLift 3193228
  have htrace : WordTrace (prefixWord ++ tailWord_3193228) baseStart_3193228 baseEnd_3193228 := by
    simpa [prefixWord, tailWord_3193228, baseEnd_3193228] using wordTrace_append hprefix tailTrace_3193228
  have hstable : (prefixWord ++ tailWord_3193228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193228).length < 2 ^ (prefixWord ++ tailWord_3193228).sum := by decide
  have hdescent : baseEnd_3193228 < baseStart_3193228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193230 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_3193230 : Nat := 118140960795 + 3193230 * 2 ^ 59
def prefixEnd_3193230 : Nat := 4983230072969 + 3 ^ 40 * 3193230 * 2
def baseEnd_3193230 : Nat := 1093107886904431137759739

theorem tailTrace_3193230 : CollatzResearch.WordTrace tailWord_3193230 prefixEnd_3193230 1093107886904431137759739 := by
  unfold tailWord_3193230
  simp only [CollatzResearch.WordTrace]
  refine ⟨14558333277685068138845143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77644444147653696740507429 14558333277685068138845143)
  ·
    refine ⟨21837499916527602208267715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14558333277685068138845143 21837499916527602208267715)
    ·
      refine ⟨32756249874791403312401573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21837499916527602208267715 32756249874791403312401573)
      ·
        refine ⟨6141796851523388121075295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32756249874791403312401573 6141796851523388121075295)
        ·
          refine ⟨9212695277285082181612943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6141796851523388121075295 9212695277285082181612943)
          ·
            refine ⟨13819042915927623272419415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9212695277285082181612943 13819042915927623272419415)
            ·
              refine ⟨20728564373891434908629123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13819042915927623272419415 20728564373891434908629123)
              ·
                refine ⟨31092846560837152362943685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20728564373891434908629123 31092846560837152362943685)
                ·
                  refine ⟨5829908730156966068051941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31092846560837152362943685 5829908730156966068051941)
                  ·
                    refine ⟨1093107886904431137759739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5829908730156966068051941 1093107886904431137759739)
                    ·
                      rfl

theorem cell22_3193230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_3193230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193230 prefixEnd_3193230 := by exact prefixLift 3193230
  have htrace : WordTrace (prefixWord ++ tailWord_3193230) baseStart_3193230 baseEnd_3193230 := by
    simpa [prefixWord, tailWord_3193230, baseEnd_3193230] using wordTrace_append hprefix tailTrace_3193230
  have hstable : (prefixWord ++ tailWord_3193230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193230).length < 2 ^ (prefixWord ++ tailWord_3193230).sum := by decide
  have hdescent : baseEnd_3193230 < baseStart_3193230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193245 : List Nat := [1, 4, 2, 1, 4, 1, 2, 7]
def baseStart_3193245 : Nat := 118140960795 + 3193245 * 2 ^ 59
def prefixEnd_3193245 : Nat := 4983230072969 + 3 ^ 40 * 3193245 * 2
def baseEnd_3193245 : Nat := 121457002412330677626077

theorem tailTrace_3193245 : CollatzResearch.WordTrace tailWord_3193245 prefixEnd_3193245 121457002412330677626077 := by
  unfold tailWord_3193245
  simp only [CollatzResearch.WordTrace]
  refine ⟨116467213316426202672557189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77644808877617468448371459 116467213316426202672557189)
  ·
    refine ⟨21837602496829913001104473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116467213316426202672557189 21837602496829913001104473)
    ·
      refine ⟨16378201872622434750828355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21837602496829913001104473 16378201872622434750828355)
      ·
        refine ⟨24567302808933652126242533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16378201872622434750828355 24567302808933652126242533)
        ·
          refine ⟨4606369276675059773670475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24567302808933652126242533 4606369276675059773670475)
          ·
            refine ⟨6909553915012589660505713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4606369276675059773670475 6909553915012589660505713)
            ·
              refine ⟨5182165436259442245379285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6909553915012589660505713 5182165436259442245379285)
              ·
                refine ⟨121457002412330677626077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5182165436259442245379285 121457002412330677626077)
                ·
                  rfl

theorem cell22_3193245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 7].length) (baseStart_3193245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193245 prefixEnd_3193245 := by exact prefixLift 3193245
  have htrace : WordTrace (prefixWord ++ tailWord_3193245) baseStart_3193245 baseEnd_3193245 := by
    simpa [prefixWord, tailWord_3193245, baseEnd_3193245] using wordTrace_append hprefix tailTrace_3193245
  have hstable : (prefixWord ++ tailWord_3193245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193245).length < 2 ^ (prefixWord ++ tailWord_3193245).sum := by decide
  have hdescent : baseEnd_3193245 < baseStart_3193245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193249 : List Nat := [1, 2, 3, 5, 1, 1, 1, 3, 2, 3]
def baseStart_3193249 : Nat := 118140960795 + 3193249 * 2 ^ 59
def prefixEnd_3193249 : Nat := 4983230072969 + 3 ^ 40 * 3193249 * 2
def baseEnd_3193249 : Nat := 1093114390992721421534681

theorem tailTrace_3193249 : CollatzResearch.WordTrace tailWord_3193249 prefixEnd_3193249 1093114390992721421534681 := by
  unfold tailWord_3193249
  simp only [CollatzResearch.WordTrace]
  refine ⟨116467359208411711355702801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77644906138941140903801867 116467359208411711355702801)
  ·
    refine ⟨87350519406308783516777101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116467359208411711355702801 87350519406308783516777101)
    ·
      refine ⟨32756444777365793818791413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87350519406308783516777101 32756444777365793818791413)
      ·
        refine ⟨3070916697878043170511695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32756444777365793818791413 3070916697878043170511695)
        ·
          refine ⟨4606375046817064755767543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3070916697878043170511695 4606375046817064755767543)
          ·
            refine ⟨6909562570225597133651315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4606375046817064755767543 6909562570225597133651315)
            ·
              refine ⟨10364343855338395700476973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6909562570225597133651315 10364343855338395700476973)
              ·
                refine ⟨3886628945751898387678865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10364343855338395700476973 3886628945751898387678865)
                ·
                  refine ⟨2914971709313923790759149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3886628945751898387678865 2914971709313923790759149)
                  ·
                    refine ⟨1093114390992721421534681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2914971709313923790759149 1093114390992721421534681)
                    ·
                      rfl

theorem cell22_3193249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_3193249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193249 prefixEnd_3193249 := by exact prefixLift 3193249
  have htrace : WordTrace (prefixWord ++ tailWord_3193249) baseStart_3193249 baseEnd_3193249 := by
    simpa [prefixWord, tailWord_3193249, baseEnd_3193249] using wordTrace_append hprefix tailTrace_3193249
  have hstable : (prefixWord ++ tailWord_3193249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193249).length < 2 ^ (prefixWord ++ tailWord_3193249).sum := by decide
  have hdescent : baseEnd_3193249 < baseStart_3193249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193290 : List Nat := [3, 1, 2, 1, 2, 2, 4, 2, 5]
def baseStart_3193290 : Nat := 118140960795 + 3193290 * 2 ^ 59
def prefixEnd_3193290 : Nat := 4983230072969 + 3 ^ 40 * 3193290 * 2
def baseEnd_3193290 : Nat := 364376142043536993753185

theorem tailTrace_3193290 : CollatzResearch.WordTrace tailWord_3193290 prefixEnd_3193290 364376142043536993753185 := by
  unfold tailWord_3193290
  simp only [CollatzResearch.WordTrace]
  refine ⟨29117213650315793839486331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77645903067508783571963549 29117213650315793839486331)
  ·
    refine ⟨43675820475473690759229497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29117213650315793839486331 43675820475473690759229497)
    ·
      refine ⟨32756865356605268069422123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43675820475473690759229497 32756865356605268069422123)
      ·
        refine ⟨49135298034907902104133185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32756865356605268069422123 49135298034907902104133185)
        ·
          refine ⟨36851473526180926578099889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49135298034907902104133185 36851473526180926578099889)
          ·
            refine ⟨27638605144635694933574917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36851473526180926578099889 27638605144635694933574917)
            ·
              refine ⟨5182238464619192800045297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27638605144635694933574917 5182238464619192800045297)
              ·
                refine ⟨3886678848464394600033973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5182238464619192800045297 3886678848464394600033973)
                ·
                  refine ⟨364376142043536993753185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3886678848464394600033973 364376142043536993753185)
                  ·
                    rfl

theorem cell22_3193290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_3193290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193290 prefixEnd_3193290 := by exact prefixLift 3193290
  have htrace : WordTrace (prefixWord ++ tailWord_3193290) baseStart_3193290 baseEnd_3193290 := by
    simpa [prefixWord, tailWord_3193290, baseEnd_3193290] using wordTrace_append hprefix tailTrace_3193290
  have hstable : (prefixWord ++ tailWord_3193290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193290).length < 2 ^ (prefixWord ++ tailWord_3193290).sum := by decide
  have hdescent : baseEnd_3193290 < baseStart_3193290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193320 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 3, 4]
def baseStart_3193320 : Nat := 118140960795 + 3193320 * 2 ^ 59
def prefixEnd_3193320 : Nat := 4983230072969 + 3 ^ 40 * 3193320 * 2
def baseEnd_3193320 : Nat := 1093138695743700903009463

theorem tailTrace_3193320 : CollatzResearch.WordTrace tailWord_3193320 prefixEnd_3193320 1093138695743700903009463 := by
  unfold tailWord_3193320
  simp only [CollatzResearch.WordTrace]
  refine ⟨58234974395577245240768707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77646632527436326987691609 58234974395577245240768707)
  ·
    refine ⟨87352461593365867861153061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58234974395577245240768707 87352461593365867861153061)
    ·
      refine ⟨16378586548756100223966199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87352461593365867861153061 16378586548756100223966199)
      ·
        refine ⟨24567879823134150335949299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16378586548756100223966199 24567879823134150335949299)
        ·
          refine ⟨36851819734701225503923949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24567879823134150335949299 36851819734701225503923949)
          ·
            refine ⟨13819432400512959563971481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36851819734701225503923949 13819432400512959563971481)
            ·
              refine ⟨10364574300384719672978611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13819432400512959563971481 10364574300384719672978611)
              ·
                refine ⟨15546861450577079509467917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10364574300384719672978611 15546861450577079509467917)
                ·
                  refine ⟨5830073043966404816050469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15546861450577079509467917 5830073043966404816050469)
                  ·
                    refine ⟨1093138695743700903009463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5830073043966404816050469 1093138695743700903009463)
                    ·
                      rfl

theorem cell22_3193320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_3193320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193320 prefixEnd_3193320 := by exact prefixLift 3193320
  have htrace : WordTrace (prefixWord ++ tailWord_3193320) baseStart_3193320 baseEnd_3193320 := by
    simpa [prefixWord, tailWord_3193320, baseEnd_3193320] using wordTrace_append hprefix tailTrace_3193320
  have hstable : (prefixWord ++ tailWord_3193320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193320).length < 2 ^ (prefixWord ++ tailWord_3193320).sum := by decide
  have hdescent : baseEnd_3193320 < baseStart_3193320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193337 : List Nat := [1, 2, 1, 3, 1, 2, 6, 1, 1, 4]
def baseStart_3193337 : Nat := 118140960795 + 3193337 * 2 ^ 59
def prefixEnd_3193337 : Nat := 4983230072969 + 3 ^ 40 * 3193337 * 2
def baseEnd_3193337 : Nat := 1093144515191118525334411

theorem tailTrace_3193337 : CollatzResearch.WordTrace tailWord_3193337 prefixEnd_3193337 1093144515191118525334411 := by
  unfold tailWord_3193337
  simp only [CollatzResearch.WordTrace]
  refine ⟨116470568832092902384906265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77647045888061934923270843 116470568832092902384906265)
  ·
    refine ⟨87352926624069676788679699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116470568832092902384906265 87352926624069676788679699)
    ·
      refine ⟨131029389936104515183019549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87352926624069676788679699 131029389936104515183019549)
      ·
        refine ⟨49136021226039193193632331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131029389936104515183019549 49136021226039193193632331)
        ·
          refine ⟨73704031839058789790448497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49136021226039193193632331 73704031839058789790448497)
          ·
            refine ⟨55278023879294092342836373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73704031839058789790448497 55278023879294092342836373)
            ·
              refine ⟨2591157369341910578570455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55278023879294092342836373 2591157369341910578570455)
              ·
                refine ⟨3886736054012865867855683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2591157369341910578570455 3886736054012865867855683)
                ·
                  refine ⟨5830104081019298801783525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3886736054012865867855683 5830104081019298801783525)
                  ·
                    refine ⟨1093144515191118525334411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5830104081019298801783525 1093144515191118525334411)
                    ·
                      rfl

theorem cell22_3193337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 1, 4].length) (baseStart_3193337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193337 prefixEnd_3193337 := by exact prefixLift 3193337
  have htrace : WordTrace (prefixWord ++ tailWord_3193337) baseStart_3193337 baseEnd_3193337 := by
    simpa [prefixWord, tailWord_3193337, baseEnd_3193337] using wordTrace_append hprefix tailTrace_3193337
  have hstable : (prefixWord ++ tailWord_3193337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193337).length < 2 ^ (prefixWord ++ tailWord_3193337).sum := by decide
  have hdescent : baseEnd_3193337 < baseStart_3193337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193363 : List Nat := [1, 1, 1, 2, 1, 5, 2, 9]
def baseStart_3193363 : Nat := 118140960795 + 3193363 * 2 ^ 59
def prefixEnd_3193363 : Nat := 4983230072969 + 3 ^ 40 * 3193363 * 2
def baseEnd_3193363 : Nat := 121461490613607013798259

theorem tailTrace_3193363 : CollatzResearch.WordTrace tailWord_3193363 prefixEnd_3193363 121461490613607013798259 := by
  unfold tailWord_3193363
  simp only [CollatzResearch.WordTrace]
  refine ⟨116471517129998708825352743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77647678086665805883568495 116471517129998708825352743)
  ·
    refine ⟨174707275694998063238029115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116471517129998708825352743 174707275694998063238029115)
    ·
      refine ⟨262060913542497094857043673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174707275694998063238029115 262060913542497094857043673)
      ·
        refine ⟨196545685156872821142782755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262060913542497094857043673 196545685156872821142782755)
        ·
          refine ⟨294818527735309231714174133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196545685156872821142782755 294818527735309231714174133)
          ·
            refine ⟨27639236975185240473203825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 294818527735309231714174133 27639236975185240473203825)
            ·
              refine ⟨20729427731388930354902869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27639236975185240473203825 20729427731388930354902869)
              ·
                refine ⟨121461490613607013798259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20729427731388930354902869 121461490613607013798259)
                ·
                  rfl

theorem cell22_3193363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 9].length) (baseStart_3193363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193363 prefixEnd_3193363 := by exact prefixLift 3193363
  have htrace : WordTrace (prefixWord ++ tailWord_3193363) baseStart_3193363 baseEnd_3193363 := by
    simpa [prefixWord, tailWord_3193363, baseEnd_3193363] using wordTrace_append hprefix tailTrace_3193363
  have hstable : (prefixWord ++ tailWord_3193363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193363).length < 2 ^ (prefixWord ++ tailWord_3193363).sum := by decide
  have hdescent : baseEnd_3193363 < baseStart_3193363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193414 : List Nat := [6, 1, 1, 1, 2, 2, 2, 7]
def baseStart_3193414 : Nat := 118140960795 + 3193414 * 2 ^ 59
def prefixEnd_3193414 : Nat := 4983230072969 + 3 ^ 40 * 3193414 * 2
def baseEnd_3193414 : Nat := 121463430429412887906575

theorem tailTrace_3193414 : CollatzResearch.WordTrace tailWord_3193414 prefixEnd_3193414 121463430429412887906575 := by
  unfold tailWord_3193414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3639793039150435766733103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77648918168542629690306197 3639793039150435766733103)
  ·
    refine ⟨5459689558725653650099655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3639793039150435766733103 5459689558725653650099655)
    ·
      refine ⟨8189534338088480475149483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5459689558725653650099655 8189534338088480475149483)
      ·
        refine ⟨12284301507132720712724225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8189534338088480475149483 12284301507132720712724225)
        ·
          refine ⟨9213226130349540534543169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12284301507132720712724225 9213226130349540534543169)
          ·
            refine ⟨6909919597762155400907377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9213226130349540534543169 6909919597762155400907377)
            ·
              refine ⟨5182439698321616550680533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6909919597762155400907377 5182439698321616550680533)
              ·
                refine ⟨121463430429412887906575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5182439698321616550680533 121463430429412887906575)
                ·
                  rfl

theorem cell22_3193414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_3193414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193414 prefixEnd_3193414 := by exact prefixLift 3193414
  have htrace : WordTrace (prefixWord ++ tailWord_3193414) baseStart_3193414 baseEnd_3193414 := by
    simpa [prefixWord, tailWord_3193414, baseEnd_3193414] using wordTrace_append hprefix tailTrace_3193414
  have hstable : (prefixWord ++ tailWord_3193414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193414).length < 2 ^ (prefixWord ++ tailWord_3193414).sum := by decide
  have hdescent : baseEnd_3193414 < baseStart_3193414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193519 : List Nat := [1, 1, 2, 1, 2, 5, 3, 2, 2, 3]
def baseStart_3193519 : Nat := 118140960795 + 3193519 * 2 ^ 59
def prefixEnd_3193519 : Nat := 4983230072969 + 3 ^ 40 * 3193519 * 2
def baseEnd_3193519 : Nat := 1093206817510530717283853

theorem tailTrace_3193519 : CollatzResearch.WordTrace tailWord_3193519 prefixEnd_3193519 1093206817510530717283853 := by
  unfold tailWord_3193519
  simp only [CollatzResearch.WordTrace]
  refine ⟨116477206917433547468031611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77651471278289031645354407 116477206917433547468031611)
  ·
    refine ⟨174715810376150321202047417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116477206917433547468031611 174715810376150321202047417)
    ·
      refine ⟨131036857782112740901535563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174715810376150321202047417 131036857782112740901535563)
      ·
        refine ⟨196555286673169111352303345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131036857782112740901535563 196555286673169111352303345)
        ·
          refine ⟨147416465004876833514227509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196555286673169111352303345 147416465004876833514227509)
          ·
            refine ⟨13820293594207203141958829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147416465004876833514227509 13820293594207203141958829)
            ·
              refine ⟨5182610097827701178234561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13820293594207203141958829 5182610097827701178234561)
              ·
                refine ⟨3886957573370775883675921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5182610097827701178234561 3886957573370775883675921)
                ·
                  refine ⟨2915218180028081912756941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3886957573370775883675921 2915218180028081912756941)
                  ·
                    refine ⟨1093206817510530717283853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2915218180028081912756941 1093206817510530717283853)
                    ·
                      rfl

theorem cell22_3193519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 3].length) (baseStart_3193519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193519 prefixEnd_3193519 := by exact prefixLift 3193519
  have htrace : WordTrace (prefixWord ++ tailWord_3193519) baseStart_3193519 baseEnd_3193519 := by
    simpa [prefixWord, tailWord_3193519, baseEnd_3193519] using wordTrace_append hprefix tailTrace_3193519
  have hstable : (prefixWord ++ tailWord_3193519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193519).length < 2 ^ (prefixWord ++ tailWord_3193519).sum := by decide
  have hdescent : baseEnd_3193519 < baseStart_3193519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193536 : List Nat := [2, 1, 1, 2, 4, 3, 3, 1, 2, 3]
def baseStart_3193536 : Nat := 118140960795 + 3193536 * 2 ^ 59
def prefixEnd_3193536 : Nat := 4983230072969 + 3 ^ 40 * 3193536 * 2
def baseEnd_3193536 : Nat := 1093212636957948339608801

theorem tailTrace_3193536 : CollatzResearch.WordTrace tailWord_3193536 prefixEnd_3193536 1093212636957948339608801 := by
  unfold tailWord_3193536
  simp only [CollatzResearch.WordTrace]
  refine ⟨58238913479185979685700231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77651884638914639580933641 58238913479185979685700231)
  ·
    refine ⟨87358370218778969528550347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58238913479185979685700231 87358370218778969528550347)
    ·
      refine ⟨131037555328168454292825521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87358370218778969528550347 131037555328168454292825521)
      ·
        refine ⟨98278166496126340719619141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131037555328168454292825521 98278166496126340719619141)
        ·
          refine ⟨18427156218023688884928589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98278166496126340719619141 18427156218023688884928589)
          ·
            refine ⟨6910183581758883331848221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18427156218023688884928589 6910183581758883331848221)
            ·
              refine ⟨2591318843159581249443083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6910183581758883331848221 2591318843159581249443083)
              ·
                refine ⟨3886978264739371874164625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2591318843159581249443083 3886978264739371874164625)
                ·
                  refine ⟨2915233698554528905623469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3886978264739371874164625 2915233698554528905623469)
                  ·
                    refine ⟨1093212636957948339608801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2915233698554528905623469 1093212636957948339608801)
                    ·
                      rfl

theorem cell22_3193536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 2, 3].length) (baseStart_3193536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193536 prefixEnd_3193536 := by exact prefixLift 3193536
  have htrace : WordTrace (prefixWord ++ tailWord_3193536) baseStart_3193536 baseEnd_3193536 := by
    simpa [prefixWord, tailWord_3193536, baseEnd_3193536] using wordTrace_append hprefix tailTrace_3193536
  have hstable : (prefixWord ++ tailWord_3193536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193536).length < 2 ^ (prefixWord ++ tailWord_3193536).sum := by decide
  have hdescent : baseEnd_3193536 < baseStart_3193536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193594 : List Nat := [3, 1, 1, 1, 1, 3, 6, 1, 5]
def baseStart_3193594 : Nat := 118140960795 + 3193594 * 2 ^ 59
def prefixEnd_3193594 : Nat := 4983230072969 + 3 ^ 40 * 3193594 * 2
def baseEnd_3193594 : Nat := 364410830514418507219541

theorem tailTrace_3193594 : CollatzResearch.WordTrace tailWord_3193594 prefixEnd_3193594 364410830514418507219541 := by
  unfold tailWord_3193594
  simp only [CollatzResearch.WordTrace]
  refine ⟨29119985598040458819252959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77653294928107890184674557 29119985598040458819252959)
  ·
    refine ⟨43679978397060688228879439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29119985598040458819252959 43679978397060688228879439)
    ·
      refine ⟨65519967595591032343319159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43679978397060688228879439 65519967595591032343319159)
      ·
        refine ⟨98279951393386548514978739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65519967595591032343319159 98279951393386548514978739)
        ·
          refine ⟨147419927090079822772468109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98279951393386548514978739 147419927090079822772468109)
          ·
            refine ⟨55282472658779933539675541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147419927090079822772468109 55282472658779933539675541)
            ·
              refine ⟨2591365905880309384672291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55282472658779933539675541 2591365905880309384672291)
              ·
                refine ⟨3887048858820464077008437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2591365905880309384672291 3887048858820464077008437)
                ·
                  refine ⟨364410830514418507219541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3887048858820464077008437 364410830514418507219541)
                  ·
                    rfl

theorem cell22_3193594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_3193594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193594 prefixEnd_3193594 := by exact prefixLift 3193594
  have htrace : WordTrace (prefixWord ++ tailWord_3193594) baseStart_3193594 baseEnd_3193594 := by
    simpa [prefixWord, tailWord_3193594, baseEnd_3193594] using wordTrace_append hprefix tailTrace_3193594
  have hstable : (prefixWord ++ tailWord_3193594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193594).length < 2 ^ (prefixWord ++ tailWord_3193594).sum := by decide
  have hdescent : baseEnd_3193594 < baseStart_3193594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193637 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_3193637 : Nat := 118140960795 + 3193637 * 2 ^ 59
def prefixEnd_3193637 : Nat := 4983230072969 + 3 ^ 40 * 3193637 * 2
def baseEnd_3193637 : Nat := 1093247211322017742833491

theorem tailTrace_3193637 : CollatzResearch.WordTrace tailWord_3193637 prefixEnd_3193637 1093247211322017742833491 := by
  unfold tailWord_3193637
  simp only [CollatzResearch.WordTrace]
  refine ⟨116481510731006053620827165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77654340487337369080551443 116481510731006053620827165)
  ·
    refine ⟨43680566524127270107810187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116481510731006053620827165 43680566524127270107810187)
    ·
      refine ⟨65520849786190905161715281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43680566524127270107810187 65520849786190905161715281)
      ·
        refine ⟨49140637339643178871286461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65520849786190905161715281 49140637339643178871286461)
        ·
          refine ⟨18427739002366192076732423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49140637339643178871286461 18427739002366192076732423)
          ·
            refine ⟨27641608503549288115098635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18427739002366192076732423 27641608503549288115098635)
            ·
              refine ⟨41462412755323932172647953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27641608503549288115098635 41462412755323932172647953)
              ·
                refine ⟨31096809566492949129485965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41462412755323932172647953 31096809566492949129485965)
                ·
                  refine ⟨11661303587434855923557237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31096809566492949129485965 11661303587434855923557237)
                  ·
                    refine ⟨1093247211322017742833491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11661303587434855923557237 1093247211322017742833491)
                    ·
                      rfl

theorem cell22_3193637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_3193637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193637 prefixEnd_3193637 := by exact prefixLift 3193637
  have htrace : WordTrace (prefixWord ++ tailWord_3193637) baseStart_3193637 baseEnd_3193637 := by
    simpa [prefixWord, tailWord_3193637, baseEnd_3193637] using wordTrace_append hprefix tailTrace_3193637
  have hstable : (prefixWord ++ tailWord_3193637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193637).length < 2 ^ (prefixWord ++ tailWord_3193637).sum := by decide
  have hdescent : baseEnd_3193637 < baseStart_3193637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193684 : List Nat := [2, 4, 1, 1, 4, 1, 9]
def baseStart_3193684 : Nat := 118140960795 + 3193684 * 2 ^ 59
def prefixEnd_3193684 : Nat := 4983230072969 + 3 ^ 40 * 3193684 * 2
def baseEnd_3193684 : Nat := 40491233347500936552161

theorem tailTrace_3193684 : CollatzResearch.WordTrace tailWord_3193684 prefixEnd_3193684 40491233347500936552161 := by
  unfold tailWord_3193684
  simp only [CollatzResearch.WordTrace]
  refine ⟨58241612480917890323894053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77655483307890520431858737 58241612480917890323894053)
  ·
    refine ⟨10920302340172104435730135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58241612480917890323894053 10920302340172104435730135)
    ·
      refine ⟨16380453510258156653595203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10920302340172104435730135 16380453510258156653595203)
      ·
        refine ⟨24570680265387234980392805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16380453510258156653595203 24570680265387234980392805)
        ·
          refine ⟨4607002549760106558823651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24570680265387234980392805 4607002549760106558823651)
          ·
            refine ⟨6910503824640159838235477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4607002549760106558823651 6910503824640159838235477)
            ·
              refine ⟨40491233347500936552161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6910503824640159838235477 40491233347500936552161)
              ·
                rfl

theorem cell22_3193684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 9].length) (baseStart_3193684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193684 prefixEnd_3193684 := by exact prefixLift 3193684
  have htrace : WordTrace (prefixWord ++ tailWord_3193684) baseStart_3193684 baseEnd_3193684 := by
    simpa [prefixWord, tailWord_3193684, baseEnd_3193684] using wordTrace_append hprefix tailTrace_3193684
  have hstable : (prefixWord ++ tailWord_3193684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193684).length < 2 ^ (prefixWord ++ tailWord_3193684).sum := by decide
  have hdescent : baseEnd_3193684 < baseStart_3193684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193697 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 2, 6]
def baseStart_3193697 : Nat := 118140960795 + 3193697 * 2 ^ 59
def prefixEnd_3193697 : Nat := 4983230072969 + 3 ^ 40 * 3193697 * 2
def baseEnd_3193697 : Nat := 1093267750548197586333307

theorem tailTrace_3193697 : CollatzResearch.WordTrace tailWord_3193697 prefixEnd_3193697 1093267750548197586333307 := by
  unfold tailWord_3193697
  simp only [CollatzResearch.WordTrace]
  refine ⟨116483699110788683868011345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77655799407192455912007563 116483699110788683868011345)
  ·
    refine ⟨87362774333091512901008509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116483699110788683868011345 87362774333091512901008509)
    ·
      refine ⟨32761040374909317337878191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87362774333091512901008509 32761040374909317337878191)
      ·
        refine ⟨49141560562363976006817287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32761040374909317337878191 49141560562363976006817287)
        ·
          refine ⟨73712340843545964010225931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49141560562363976006817287 73712340843545964010225931)
          ·
            refine ⟨110568511265318946015338897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73712340843545964010225931 110568511265318946015338897)
            ·
              refine ⟨82926383448989209511504173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110568511265318946015338897 82926383448989209511504173)
              ·
                refine ⟨31097393793370953566814065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82926383448989209511504173 31097393793370953566814065)
                ·
                  refine ⟨23323045345028215175110549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31097393793370953566814065 23323045345028215175110549)
                  ·
                    refine ⟨1093267750548197586333307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23323045345028215175110549 1093267750548197586333307)
                    ·
                      rfl

theorem cell22_3193697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_3193697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193697 prefixEnd_3193697 := by exact prefixLift 3193697
  have htrace : WordTrace (prefixWord ++ tailWord_3193697) baseStart_3193697 baseEnd_3193697 := by
    simpa [prefixWord, tailWord_3193697, baseEnd_3193697] using wordTrace_append hprefix tailTrace_3193697
  have hstable : (prefixWord ++ tailWord_3193697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193697).length < 2 ^ (prefixWord ++ tailWord_3193697).sum := by decide
  have hdescent : baseEnd_3193697 < baseStart_3193697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193718 : List Nat := [5, 1, 1, 3, 1, 3, 2, 6]
def baseStart_3193718 : Nat := 118140960795 + 3193718 * 2 ^ 59
def prefixEnd_3193718 : Nat := 4983230072969 + 3 ^ 40 * 3193718 * 2
def baseEnd_3193718 : Nat := 121474993253040059062027

theorem tailTrace_3193718 : CollatzResearch.WordTrace tailWord_3193718 prefixEnd_3193718 121474993253040059062027 := by
  unfold tailWord_3193718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7280279065232037778407863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77656310029141736303017205 7280279065232037778407863)
  ·
    refine ⟨10920418597848056667611795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7280279065232037778407863 10920418597848056667611795)
    ·
      refine ⟨16380627896772085001417693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10920418597848056667611795 16380627896772085001417693)
      ·
        refine ⟨6142735461289531875531635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16380627896772085001417693 6142735461289531875531635)
        ·
          refine ⟨9214103191934297813297453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6142735461289531875531635 9214103191934297813297453)
          ·
            refine ⟨3455288696975361679986545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9214103191934297813297453 3455288696975361679986545)
            ·
              refine ⟨2591466522731521259989909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3455288696975361679986545 2591466522731521259989909)
              ·
                refine ⟨121474993253040059062027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2591466522731521259989909 121474993253040059062027)
                ·
                  rfl

theorem cell22_3193718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_3193718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193718 prefixEnd_3193718 := by exact prefixLift 3193718
  have htrace : WordTrace (prefixWord ++ tailWord_3193718) baseStart_3193718 baseEnd_3193718 := by
    simpa [prefixWord, tailWord_3193718, baseEnd_3193718] using wordTrace_append hprefix tailTrace_3193718
  have hstable : (prefixWord ++ tailWord_3193718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193718).length < 2 ^ (prefixWord ++ tailWord_3193718).sum := by decide
  have hdescent : baseEnd_3193718 < baseStart_3193718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193727 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 1, 7]
def baseStart_3193727 : Nat := 118140960795 + 3193727 * 2 ^ 59
def prefixEnd_3193727 : Nat := 4983230072969 + 3 ^ 40 * 3193727 * 2
def baseEnd_3193727 : Nat := 1093278020161287508083215

theorem tailTrace_3193727 : CollatzResearch.WordTrace tailWord_3193727 prefixEnd_3193727 1093278020161287508083215 := by
  unfold tailWord_3193727
  simp only [CollatzResearch.WordTrace]
  refine ⟨116484793300679998991603435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77656528867119999327735623 116484793300679998991603435)
  ·
    refine ⟨174727189951019998487405153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116484793300679998991603435 174727189951019998487405153)
    ·
      refine ⟨131045392463264998865553865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174727189951019998487405153 131045392463264998865553865)
      ·
        refine ⟨98284044347448749149165399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131045392463264998865553865 98284044347448749149165399)
        ·
          refine ⟨147426066521173123723748099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98284044347448749149165399 147426066521173123723748099)
          ·
            refine ⟨221139099781759685585622149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147426066521173123723748099 221139099781759685585622149)
            ·
              refine ⟨41463581209079941047304153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221139099781759685585622149 41463581209079941047304153)
              ·
                refine ⟨31097685906809955785478115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41463581209079941047304153 31097685906809955785478115)
                ·
                  refine ⟨46646528860214933678217173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31097685906809955785478115 46646528860214933678217173)
                  ·
                    refine ⟨1093278020161287508083215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46646528860214933678217173 1093278020161287508083215)
                    ·
                      rfl

theorem cell22_3193727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_3193727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193727 prefixEnd_3193727 := by exact prefixLift 3193727
  have htrace : WordTrace (prefixWord ++ tailWord_3193727) baseStart_3193727 baseEnd_3193727 := by
    simpa [prefixWord, tailWord_3193727, baseEnd_3193727] using wordTrace_append hprefix tailTrace_3193727
  have hstable : (prefixWord ++ tailWord_3193727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193727).length < 2 ^ (prefixWord ++ tailWord_3193727).sum := by decide
  have hdescent : baseEnd_3193727 < baseStart_3193727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193733 : List Nat := [1, 3, 1, 1, 3, 3, 3, 3, 1, 3]
def baseStart_3193733 : Nat := 118140960795 + 3193733 * 2 ^ 59
def prefixEnd_3193733 : Nat := 4983230072969 + 3 ^ 40 * 3193733 * 2
def baseEnd_3193733 : Nat := 1093280074083905492433197

theorem tailTrace_3193733 : CollatzResearch.WordTrace tailWord_3193733 prefixEnd_3193733 1093280074083905492433197 := by
  unfold tailWord_3193733
  simp only [CollatzResearch.WordTrace]
  refine ⟨116485012138658262016321853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77656674759105508010881235 116485012138658262016321853)
  ·
    refine ⟨43681879551996848256120695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116485012138658262016321853 43681879551996848256120695)
    ·
      refine ⟨65522819327995272384181043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43681879551996848256120695 65522819327995272384181043)
      ·
        refine ⟨98284228991992908576271565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65522819327995272384181043 98284228991992908576271565)
        ·
          refine ⟨36856585871997340716101837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98284228991992908576271565 36856585871997340716101837)
          ·
            refine ⟨13821219701999002768538189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36856585871997340716101837 13821219701999002768538189)
            ·
              refine ⟨5182957388249626038201821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13821219701999002768538189 5182957388249626038201821)
              ·
                refine ⟨1943609020593609764325683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5182957388249626038201821 1943609020593609764325683)
                ·
                  refine ⟨2915413530890414646488525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943609020593609764325683 2915413530890414646488525)
                  ·
                    refine ⟨1093280074083905492433197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2915413530890414646488525 1093280074083905492433197)
                    ·
                      rfl

theorem cell22_3193733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_3193733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193733 prefixEnd_3193733 := by exact prefixLift 3193733
  have htrace : WordTrace (prefixWord ++ tailWord_3193733) baseStart_3193733 baseEnd_3193733 := by
    simpa [prefixWord, tailWord_3193733, baseEnd_3193733] using wordTrace_append hprefix tailTrace_3193733
  have hstable : (prefixWord ++ tailWord_3193733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193733).length < 2 ^ (prefixWord ++ tailWord_3193733).sum := by decide
  have hdescent : baseEnd_3193733 < baseStart_3193733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193844 : List Nat := [2, 6, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3193844 : Nat := 118140960795 + 3193844 * 2 ^ 59
def prefixEnd_3193844 : Nat := 4983230072969 + 3 ^ 40 * 3193844 * 2
def baseEnd_3193844 : Nat := 1093318071652338202907857

theorem tailTrace_3193844 : CollatzResearch.WordTrace tailWord_3193844 prefixEnd_3193844 1093318071652338202907857 := by
  unfold tailWord_3193844
  simp only [CollatzResearch.WordTrace]
  refine ⟨58244530320628063986806293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77659373760837418649075057 58244530320628063986806293)
  ·
    refine ⟨2730212358779440499381545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58244530320628063986806293 2730212358779440499381545)
    ·
      refine ⟨2047659269084580374536159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2730212358779440499381545 2047659269084580374536159)
      ·
        refine ⟨3071488903626870561804239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2047659269084580374536159 3071488903626870561804239)
        ·
          refine ⟨4607233355440305842706359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3071488903626870561804239 4607233355440305842706359)
          ·
            refine ⟨6910850033160458764059539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4607233355440305842706359 6910850033160458764059539)
            ·
              refine ⟨10366275049740688146089309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6910850033160458764059539 10366275049740688146089309)
              ·
                refine ⟨3887353143652758054783491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10366275049740688146089309 3887353143652758054783491)
                ·
                  refine ⟨5831029715479137082175237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3887353143652758054783491 5831029715479137082175237)
                  ·
                    refine ⟨1093318071652338202907857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5831029715479137082175237 1093318071652338202907857)
                    ·
                      rfl

theorem cell22_3193844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3193844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193844 prefixEnd_3193844 := by exact prefixLift 3193844
  have htrace : WordTrace (prefixWord ++ tailWord_3193844) baseStart_3193844 baseEnd_3193844 := by
    simpa [prefixWord, tailWord_3193844, baseEnd_3193844] using wordTrace_append hprefix tailTrace_3193844
  have hstable : (prefixWord ++ tailWord_3193844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193844).length < 2 ^ (prefixWord ++ tailWord_3193844).sum := by decide
  have hdescent : baseEnd_3193844 < baseStart_3193844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193868 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 3, 3]
def baseStart_3193868 : Nat := 118140960795 + 3193868 * 2 ^ 59
def prefixEnd_3193868 : Nat := 4983230072969 + 3 ^ 40 * 3193868 * 2
def baseEnd_3193868 : Nat := 1093326287342810140307783

theorem tailTrace_3193868 : CollatzResearch.WordTrace tailWord_3193868 prefixEnd_3193868 1093326287342810140307783 := by
  unfold tailWord_3193868
  simp only [CollatzResearch.WordTrace]
  refine ⟨58244967996584590036243129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77659957328779453381657505 58244967996584590036243129)
  ·
    refine ⟨43683725997438442527182347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58244967996584590036243129 43683725997438442527182347)
    ·
      refine ⟨65525588996157663790773521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43683725997438442527182347 65525588996157663790773521)
      ·
        refine ⟨49144191747118247843080141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65525588996157663790773521 49144191747118247843080141)
        ·
          refine ⟨18429071905169342941155053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49144191747118247843080141 18429071905169342941155053)
          ·
            refine ⟨6910901964438503602933145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18429071905169342941155053 6910901964438503602933145)
            ·
              refine ⟨5183176473328877702199859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6910901964438503602933145 5183176473328877702199859)
              ·
                refine ⟨7774764709993316553299789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5183176473328877702199859 7774764709993316553299789)
                ·
                  refine ⟨2915536766247493707487421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7774764709993316553299789 2915536766247493707487421)
                  ·
                    refine ⟨1093326287342810140307783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2915536766247493707487421 1093326287342810140307783)
                    ·
                      rfl

theorem cell22_3193868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_3193868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193868 prefixEnd_3193868 := by exact prefixLift 3193868
  have htrace : WordTrace (prefixWord ++ tailWord_3193868) baseStart_3193868 baseEnd_3193868 := by
    simpa [prefixWord, tailWord_3193868, baseEnd_3193868] using wordTrace_append hprefix tailTrace_3193868
  have hstable : (prefixWord ++ tailWord_3193868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193868).length < 2 ^ (prefixWord ++ tailWord_3193868).sum := by decide
  have hdescent : baseEnd_3193868 < baseStart_3193868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
