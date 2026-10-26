import V185TrunkScan23Chunk1240

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7351363 : List Nat := [1, 1, 1, 3, 1, 2, 4, 4, 2, 1, 3]
def baseStart_7351363 : Nat := 118140960795 + 7351363 * 2 ^ 59
def prefixEnd_7351363 : Nat := 4983230072969 + 3 ^ 40 * 7351363 * 2
def baseEnd_7351363 : Nat := 3774782684678426492154203

theorem tailTrace_7351363 : CollatzResearch.WordTrace tailWord_7351363 prefixEnd_7351363 3774782684678426492154203 := by
  unfold tailWord_7351363
  simp only [CollatzResearch.WordTrace]
  refine ⟨268126236066274838689026743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178750824044183225792684495 268126236066274838689026743)
  ·
    refine ⟨402189354099412258033540115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268126236066274838689026743 402189354099412258033540115)
    ·
      refine ⟨603284031149118387050310173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402189354099412258033540115 603284031149118387050310173)
      ·
        refine ⟨226231511680919395143866315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 603284031149118387050310173 226231511680919395143866315)
        ·
          refine ⟨339347267521379092715799473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226231511680919395143866315 339347267521379092715799473)
          ·
            refine ⟨254510450641034319536849605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339347267521379092715799473 254510450641034319536849605)
            ·
              refine ⟨47720709495193934913159301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254510450641034319536849605 47720709495193934913159301)
              ·
                refine ⟨8947633030348862796217369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47720709495193934913159301 8947633030348862796217369)
                ·
                  refine ⟨6710724772761647097163027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8947633030348862796217369 6710724772761647097163027)
                  ·
                    refine ⟨10066087159142470645744541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6710724772761647097163027 10066087159142470645744541)
                    ·
                      refine ⟨3774782684678426492154203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10066087159142470645744541 3774782684678426492154203)
                      ·
                        rfl

theorem cell23_7351363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_7351363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351363 prefixEnd_7351363 := by exact prefixLift 7351363
  have htrace : WordTrace (prefixWord ++ tailWord_7351363) baseStart_7351363 baseEnd_7351363 := by
    simpa [prefixWord, tailWord_7351363, baseEnd_7351363] using wordTrace_append hprefix tailTrace_7351363
  have hstable : (prefixWord ++ tailWord_7351363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351363).length < 2 ^ (prefixWord ++ tailWord_7351363).sum := by decide
  have hdescent : baseEnd_7351363 < baseStart_7351363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351409 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 11]
def baseStart_7351409 : Nat := 118140960795 + 7351409 * 2 ^ 59
def prefixEnd_7351409 : Nat := 4983230072969 + 3 ^ 40 * 7351409 * 2
def baseEnd_7351409 : Nat := 419422922754281479130999

theorem tailTrace_7351409 : CollatzResearch.WordTrace tailWord_7351409 prefixEnd_7351409 419422922754281479130999 := by
  unfold tailWord_7351409
  simp only [CollatzResearch.WordTrace]
  refine ⟨268127913824108188545201281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178751942549405459030134187 268127913824108188545201281)
  ·
    refine ⟨201095935368081141408900961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268127913824108188545201281 201095935368081141408900961)
    ·
      refine ⟨150821951526060856056675721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201095935368081141408900961 150821951526060856056675721)
      ·
        refine ⟨113116463644545642042506791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150821951526060856056675721 113116463644545642042506791)
        ·
          refine ⟨169674695466818463063760187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113116463644545642042506791 169674695466818463063760187)
          ·
            refine ⟨254512043200227694595640281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169674695466818463063760187 254512043200227694595640281)
            ·
              refine ⟨190884032400170770946730211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254512043200227694595640281 190884032400170770946730211)
              ·
                refine ⟨286326048600256156420095317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190884032400170770946730211 286326048600256156420095317)
                ·
                  refine ⟨419422922754281479130999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 286326048600256156420095317 419422922754281479130999)
                  ·
                    rfl

theorem cell23_7351409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 11].length) (baseStart_7351409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351409 prefixEnd_7351409 := by exact prefixLift 7351409
  have htrace : WordTrace (prefixWord ++ tailWord_7351409) baseStart_7351409 baseEnd_7351409 := by
    simpa [prefixWord, tailWord_7351409, baseEnd_7351409] using wordTrace_append hprefix tailTrace_7351409
  have hstable : (prefixWord ++ tailWord_7351409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351409).length < 2 ^ (prefixWord ++ tailWord_7351409).sum := by decide
  have hdescent : baseEnd_7351409 < baseStart_7351409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351419 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 7]
def baseStart_7351419 : Nat := 118140960795 + 7351419 * 2 ^ 59
def prefixEnd_7351419 : Nat := 4983230072969 + 3 ^ 40 * 7351419 * 2
def baseEnd_7351419 : Nat := 3774811439595078273053945

theorem tailTrace_7351419 : CollatzResearch.WordTrace tailWord_7351419 prefixEnd_7351419 3774811439595078273053945 := by
  unfold tailWord_7351419
  simp only [CollatzResearch.WordTrace]
  refine ⟨268128278554071960253065311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178752185702714640168710207 268128278554071960253065311)
  ·
    refine ⟨402192417831107940379597967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268128278554071960253065311 402192417831107940379597967)
    ·
      refine ⟨603288626746661910569396951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402192417831107940379597967 603288626746661910569396951)
      ·
        refine ⟨904932940119992865854095427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603288626746661910569396951 904932940119992865854095427)
        ·
          refine ⟨1357399410179989298781143141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904932940119992865854095427 1357399410179989298781143141)
          ·
            refine ⟨254512389408747993521464339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1357399410179989298781143141 254512389408747993521464339)
            ·
              refine ⟨381768584113121990282196509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254512389408747993521464339 381768584113121990282196509)
              ·
                refine ⟨143163219042420746355823691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 381768584113121990282196509 143163219042420746355823691)
                ·
                  refine ⟨214744828563631119533735537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143163219042420746355823691 214744828563631119533735537)
                  ·
                    refine ⟨161058621422723339650301653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 214744828563631119533735537 161058621422723339650301653)
                    ·
                      refine ⟨3774811439595078273053945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161058621422723339650301653 3774811439595078273053945)
                      ·
                        rfl

theorem cell23_7351419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_7351419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351419 prefixEnd_7351419 := by exact prefixLift 7351419
  have htrace : WordTrace (prefixWord ++ tailWord_7351419) baseStart_7351419 baseEnd_7351419 := by
    simpa [prefixWord, tailWord_7351419, baseEnd_7351419] using wordTrace_append hprefix tailTrace_7351419
  have hstable : (prefixWord ++ tailWord_7351419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351419).length < 2 ^ (prefixWord ++ tailWord_7351419).sum := by decide
  have hdescent : baseEnd_7351419 < baseStart_7351419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351439 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 2, 11]
def baseStart_7351439 : Nat := 118140960795 + 7351439 * 2 ^ 59
def prefixEnd_7351439 : Nat := 4983230072969 + 3 ^ 40 * 7351439 * 2
def baseEnd_7351439 : Nat := 1258273903069389398267951

theorem tailTrace_7351439 : CollatzResearch.WordTrace tailWord_7351439 prefixEnd_7351439 1258273903069389398267951 := by
  unfold tailWord_7351439
  simp only [CollatzResearch.WordTrace]
  refine ⟨268129008013999503668793371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178752672009333002445862247 268129008013999503668793371)
  ·
    refine ⟨402193512020999255503190057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268129008013999503668793371 402193512020999255503190057)
    ·
      refine ⟨301645134015749441627392543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402193512020999255503190057 301645134015749441627392543)
      ·
        refine ⟨452467701023624162441088815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301645134015749441627392543 452467701023624162441088815)
        ·
          refine ⟨678701551535436243661633223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452467701023624162441088815 678701551535436243661633223)
          ·
            refine ⟨1018052327303154365492449835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678701551535436243661633223 1018052327303154365492449835)
            ·
              refine ⟨1527078490954731548238674753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018052327303154365492449835 1527078490954731548238674753)
              ·
                refine ⟨1145308868216048661179006065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527078490954731548238674753 1145308868216048661179006065)
                ·
                  refine ⟨858981651162036495884254549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1145308868216048661179006065 858981651162036495884254549)
                  ·
                    refine ⟨1258273903069389398267951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 858981651162036495884254549 1258273903069389398267951)
                    ·
                      rfl

theorem cell23_7351439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_7351439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351439 prefixEnd_7351439 := by exact prefixLift 7351439
  have htrace : WordTrace (prefixWord ++ tailWord_7351439) baseStart_7351439 baseEnd_7351439 := by
    simpa [prefixWord, tailWord_7351439, baseEnd_7351439] using wordTrace_append hprefix tailTrace_7351439
  have hstable : (prefixWord ++ tailWord_7351439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351439).length < 2 ^ (prefixWord ++ tailWord_7351439).sum := by decide
  have hdescent : baseEnd_7351439 < baseStart_7351439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351456 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 1, 7]
def baseStart_7351456 : Nat := 118140960795 + 7351456 * 2 ^ 59
def prefixEnd_7351456 : Nat := 4983230072969 + 3 ^ 40 * 7351456 * 2
def baseEnd_7351456 : Nat := 1258276812793098209430425

theorem tailTrace_7351456 : CollatzResearch.WordTrace tailWord_7351456 prefixEnd_7351456 1258276812793098209430425 := by
  unfold tailWord_7351456
  simp only [CollatzResearch.WordTrace]
  refine ⟨134064814027468957786081111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178753085369958610381441481 134064814027468957786081111)
  ·
    refine ⟨201097221041203436679121667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134064814027468957786081111 201097221041203436679121667)
    ·
      refine ⟨301645831561805155018682501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201097221041203436679121667 301645831561805155018682501)
      ·
        refine ⟨56558593417838466566002969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301645831561805155018682501 56558593417838466566002969)
        ·
          refine ⟨42418945063378849924502227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56558593417838466566002969 42418945063378849924502227)
          ·
            refine ⟨63628417595068274886753341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42418945063378849924502227 63628417595068274886753341)
            ·
              refine ⟨23860656598150603082532503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63628417595068274886753341 23860656598150603082532503)
              ·
                refine ⟨35790984897225904623798755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23860656598150603082532503 35790984897225904623798755)
                ·
                  refine ⟨53686477345838856935698133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35790984897225904623798755 53686477345838856935698133)
                  ·
                    refine ⟨1258276812793098209430425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53686477345838856935698133 1258276812793098209430425)
                    ·
                      rfl

theorem cell23_7351456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 7].length) (baseStart_7351456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351456 prefixEnd_7351456 := by exact prefixLift 7351456
  have htrace : WordTrace (prefixWord ++ tailWord_7351456) baseStart_7351456 baseEnd_7351456 := by
    simpa [prefixWord, tailWord_7351456, baseEnd_7351456] using wordTrace_append hprefix tailTrace_7351456
  have hstable : (prefixWord ++ tailWord_7351456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351456).length < 2 ^ (prefixWord ++ tailWord_7351456).sum := by decide
  have hdescent : baseEnd_7351456 < baseStart_7351456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351460 : List Nat := [2, 3, 1, 2, 3, 2, 2, 3, 5]
def baseStart_7351460 : Nat := 118140960795 + 7351460 * 2 ^ 59
def prefixEnd_7351460 : Nat := 4983230072969 + 3 ^ 40 * 7351460 * 2
def baseEnd_7351460 : Nat := 419425832477990290293473

theorem tailTrace_7351460 : CollatzResearch.WordTrace tailWord_7351460 prefixEnd_7351460 419425832477990290293473 := by
  unfold tailWord_7351460
  simp only [CollatzResearch.WordTrace]
  refine ⟨134064886973461712127653917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178753182631282282836871889 134064886973461712127653917)
  ·
    refine ⟨50274332615048142047870219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134064886973461712127653917 50274332615048142047870219)
    ·
      refine ⟨75411498922572213071805329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50274332615048142047870219 75411498922572213071805329)
      ·
        refine ⟨56558624191929159803853997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75411498922572213071805329 56558624191929159803853997)
        ·
          refine ⟨21209484071973434926445249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56558624191929159803853997 21209484071973434926445249)
          ·
            refine ⟨15907113053980076194833937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21209484071973434926445249 15907113053980076194833937)
            ·
              refine ⟨11930334790485057146125453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15907113053980076194833937 11930334790485057146125453)
              ·
                refine ⟨4473875546431896429797045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11930334790485057146125453 4473875546431896429797045)
                ·
                  refine ⟨419425832477990290293473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4473875546431896429797045 419425832477990290293473)
                  ·
                    rfl

theorem cell23_7351460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_7351460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351460 prefixEnd_7351460 := by exact prefixLift 7351460
  have htrace : WordTrace (prefixWord ++ tailWord_7351460) baseStart_7351460 baseEnd_7351460 := by
    simpa [prefixWord, tailWord_7351460, baseEnd_7351460] using wordTrace_append hprefix tailTrace_7351460
  have hstable : (prefixWord ++ tailWord_7351460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351460).length < 2 ^ (prefixWord ++ tailWord_7351460).sum := by decide
  have hdescent : baseEnd_7351460 < baseStart_7351460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351513 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 2, 2, 3]
def baseStart_7351513 : Nat := 118140960795 + 7351513 * 2 ^ 59
def prefixEnd_7351513 : Nat := 4983230072969 + 3 ^ 40 * 7351513 * 2
def baseEnd_7351513 : Nat := 3774859706776600905278513

theorem tailTrace_7351513 : CollatzResearch.WordTrace tailWord_7351513 prefixEnd_7351513 3774859706776600905278513 := by
  unfold tailWord_7351513
  simp only [CollatzResearch.WordTrace]
  refine ⟨268131707015731414306987193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178754471343820942871324795 268131707015731414306987193)
  ·
    refine ⟨201098780261798560730240395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268131707015731414306987193 201098780261798560730240395)
    ·
      refine ⟨301648170392697841095360593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201098780261798560730240395 301648170392697841095360593)
      ·
        refine ⟨226236127794523380821520445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301648170392697841095360593 226236127794523380821520445)
        ·
          refine ⟨84838547922946267808070167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226236127794523380821520445 84838547922946267808070167)
          ·
            refine ⟨127257821884419401712105251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84838547922946267808070167 127257821884419401712105251)
            ·
              refine ⟨190886732826629102568157877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127257821884419401712105251 190886732826629102568157877)
              ·
                refine ⟨17895631202496478365764801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190886732826629102568157877 17895631202496478365764801)
                ·
                  refine ⟨13421723401872358774323601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17895631202496478365764801 13421723401872358774323601)
                  ·
                    refine ⟨10066292551404269080742701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13421723401872358774323601 10066292551404269080742701)
                    ·
                      refine ⟨3774859706776600905278513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10066292551404269080742701 3774859706776600905278513)
                      ·
                        rfl

theorem cell23_7351513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_7351513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351513 prefixEnd_7351513 := by exact prefixLift 7351513
  have htrace : WordTrace (prefixWord ++ tailWord_7351513) baseStart_7351513 baseEnd_7351513 := by
    simpa [prefixWord, tailWord_7351513, baseEnd_7351513] using wordTrace_append hprefix tailTrace_7351513
  have hstable : (prefixWord ++ tailWord_7351513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351513).length < 2 ^ (prefixWord ++ tailWord_7351513).sum := by decide
  have hdescent : baseEnd_7351513 < baseStart_7351513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351530 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_7351530 : Nat := 118140960795 + 7351530 * 2 ^ 59
def prefixEnd_7351530 : Nat := 4983230072969 + 3 ^ 40 * 7351530 * 2
def baseEnd_7351530 : Nat := 3774868435947727338765935

theorem tailTrace_7351530 : CollatzResearch.WordTrace tailWord_7351530 prefixEnd_7351530 3774868435947727338765935 := by
  unfold tailWord_7351530
  simp only [CollatzResearch.WordTrace]
  refine ⟨67033081764167456552589011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178754884704446550806904029 67033081764167456552589011)
  ·
    refine ⟨100549622646251184828883517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67033081764167456552589011 100549622646251184828883517)
    ·
      refine ⟨37706108492344194310831319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100549622646251184828883517 37706108492344194310831319)
      ·
        refine ⟨56559162738516291466246979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37706108492344194310831319 56559162738516291466246979)
        ·
          refine ⟨84838744107774437199370469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56559162738516291466246979 84838744107774437199370469)
          ·
            refine ⟨15907264520207706974881963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84838744107774437199370469 15907264520207706974881963)
            ·
              refine ⟨23860896780311560462322945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15907264520207706974881963 23860896780311560462322945)
              ·
                refine ⟨17895672585233670346742209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23860896780311560462322945 17895672585233670346742209)
                ·
                  refine ⟨13421754438925252760056657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17895672585233670346742209 13421754438925252760056657)
                  ·
                    refine ⟨10066315829193939570042493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13421754438925252760056657 10066315829193939570042493)
                    ·
                      refine ⟨3774868435947727338765935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10066315829193939570042493 3774868435947727338765935)
                      ·
                        rfl

theorem cell23_7351530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_7351530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351530 prefixEnd_7351530 := by exact prefixLift 7351530
  have htrace : WordTrace (prefixWord ++ tailWord_7351530) baseStart_7351530 baseEnd_7351530 := by
    simpa [prefixWord, tailWord_7351530, baseEnd_7351530] using wordTrace_append hprefix tailTrace_7351530
  have hstable : (prefixWord ++ tailWord_7351530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351530).length < 2 ^ (prefixWord ++ tailWord_7351530).sum := by decide
  have hdescent : baseEnd_7351530 < baseStart_7351530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351533 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 8]
def baseStart_7351533 : Nat := 118140960795 + 7351533 * 2 ^ 59
def prefixEnd_7351533 : Nat := 4983230072969 + 3 ^ 40 * 7351533 * 2
def baseEnd_7351533 : Nat := 419429997376632314114269

theorem tailTrace_7351533 : CollatzResearch.WordTrace tailWord_7351533 prefixEnd_7351533 419429997376632314114269 := by
  unfold tailWord_7351533
  simp only [CollatzResearch.WordTrace]
  refine ⟨268132436475658957722715253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178754957650439305148476835 268132436475658957722715253)
  ·
    refine ⟨25137415919593027286504555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268132436475658957722715253 25137415919593027286504555)
    ·
      refine ⟨37706123879389540929756833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25137415919593027286504555 37706123879389540929756833)
      ·
        refine ⟨28279592909542155697317625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37706123879389540929756833 28279592909542155697317625)
        ·
          refine ⟨21209694682156616772988219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28279592909542155697317625 21209694682156616772988219)
          ·
            refine ⟨31814542023234925159482329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21209694682156616772988219 31814542023234925159482329)
            ·
              refine ⟨23860906517426193869611747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31814542023234925159482329 23860906517426193869611747)
              ·
                refine ⟨35791359776139290804417621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23860906517426193869611747 35791359776139290804417621)
                ·
                  refine ⟨419429997376632314114269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35791359776139290804417621 419429997376632314114269)
                  ·
                    rfl

theorem cell23_7351533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_7351533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351533 prefixEnd_7351533 := by exact prefixLift 7351533
  have htrace : WordTrace (prefixWord ++ tailWord_7351533) baseStart_7351533 baseEnd_7351533 := by
    simpa [prefixWord, tailWord_7351533, baseEnd_7351533] using wordTrace_append hprefix tailTrace_7351533
  have hstable : (prefixWord ++ tailWord_7351533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351533).length < 2 ^ (prefixWord ++ tailWord_7351533).sum := by decide
  have hdescent : baseEnd_7351533 < baseStart_7351533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351550 : List Nat := [4, 2, 2, 1, 1, 3, 1, 3, 6]
def baseStart_7351550 : Nat := 118140960795 + 7351550 * 2 ^ 59
def prefixEnd_7351550 : Nat := 4983230072969 + 3 ^ 40 * 7351550 * 2
def baseEnd_7351550 : Nat := 419430967284535251168427

theorem tailTrace_7351550 : CollatzResearch.WordTrace tailWord_7351550 prefixEnd_7351550 419430967284535251168427 := by
  unfold tailWord_7351550
  simp only [CollatzResearch.WordTrace]
  refine ⟨33516632064574671203260513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178755371011064913084056069 33516632064574671203260513)
  ·
    refine ⟨25137474048431003402445385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33516632064574671203260513 25137474048431003402445385)
    ·
      refine ⟨18853105536323252551834039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25137474048431003402445385 18853105536323252551834039)
      ·
        refine ⟨28279658304484878827751059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18853105536323252551834039 28279658304484878827751059)
        ·
          refine ⟨42419487456727318241626589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28279658304484878827751059 42419487456727318241626589)
          ·
            refine ⟨15907307796272744340609971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42419487456727318241626589 15907307796272744340609971)
            ·
              refine ⟨23860961694409116510914957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15907307796272744340609971 23860961694409116510914957)
              ·
                refine ⟨8947860635403418691593109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23860961694409116510914957 8947860635403418691593109)
                ·
                  refine ⟨419430967284535251168427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8947860635403418691593109 419430967284535251168427)
                  ·
                    rfl

theorem cell23_7351550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_7351550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351550 prefixEnd_7351550 := by exact prefixLift 7351550
  have htrace : WordTrace (prefixWord ++ tailWord_7351550) baseStart_7351550 baseEnd_7351550 := by
    simpa [prefixWord, tailWord_7351550, baseEnd_7351550] using wordTrace_append hprefix tailTrace_7351550
  have hstable : (prefixWord ++ tailWord_7351550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351550).length < 2 ^ (prefixWord ++ tailWord_7351550).sum := by decide
  have hdescent : baseEnd_7351550 < baseStart_7351550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351563 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 3, 5]
def baseStart_7351563 : Nat := 118140960795 + 7351563 * 2 ^ 59
def prefixEnd_7351563 : Nat := 4983230072969 + 3 ^ 40 * 7351563 * 2
def baseEnd_7351563 : Nat := 1258295126936441903217761

theorem tailTrace_7351563 : CollatzResearch.WordTrace tailWord_7351563 prefixEnd_7351563 1258295126936441903217761 := by
  unfold tailWord_7351563
  simp only [CollatzResearch.WordTrace]
  refine ⟨268133530665550272846307343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178755687110366848564204895 268133530665550272846307343)
  ·
    refine ⟨402200295998325409269461015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268133530665550272846307343 402200295998325409269461015)
    ·
      refine ⟨603300443997488113904191523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402200295998325409269461015 603300443997488113904191523)
      ·
        refine ⟨904950665996232170856287285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603300443997488113904191523 904950665996232170856287285)
        ·
          refine ⟨84839124937146766017776933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 904950665996232170856287285 84839124937146766017776933)
          ·
            refine ⟨15907335925715018628333175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84839124937146766017776933 15907335925715018628333175)
            ·
              refine ⟨23861003888572527942499763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15907335925715018628333175 23861003888572527942499763)
              ·
                refine ⟨35791505832858791913749645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23861003888572527942499763 35791505832858791913749645)
                ·
                  refine ⟨13421814687322046967656117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35791505832858791913749645 13421814687322046967656117)
                  ·
                    refine ⟨1258295126936441903217761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13421814687322046967656117 1258295126936441903217761)
                    ·
                      rfl

theorem cell23_7351563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 5].length) (baseStart_7351563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351563 prefixEnd_7351563 := by exact prefixLift 7351563
  have htrace : WordTrace (prefixWord ++ tailWord_7351563) baseStart_7351563 baseEnd_7351563 := by
    simpa [prefixWord, tailWord_7351563, baseEnd_7351563] using wordTrace_append hprefix tailTrace_7351563
  have hstable : (prefixWord ++ tailWord_7351563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351563).length < 2 ^ (prefixWord ++ tailWord_7351563).sum := by decide
  have hdescent : baseEnd_7351563 < baseStart_7351563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351610 : List Nat := [3, 1, 1, 1, 4, 1, 1, 5, 2, 4]
def baseStart_7351610 : Nat := 118140960795 + 7351610 * 2 ^ 59
def prefixEnd_7351610 : Nat := 4983230072969 + 3 ^ 40 * 7351610 * 2
def baseEnd_7351610 : Nat := 1258303171466695675255189

theorem tailTrace_7351610 : CollatzResearch.WordTrace tailWord_7351610 prefixEnd_7351610 1258303171466695675255189 := by
  unfold tailWord_7351610
  simp only [CollatzResearch.WordTrace]
  refine ⟨67033811224094999968317071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178756829930919999915512189 67033811224094999968317071)
  ·
    refine ⟨100550716836142499952475607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67033811224094999968317071 100550716836142499952475607)
    ·
      refine ⟨150826075254213749928713411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100550716836142499952475607 150826075254213749928713411)
      ·
        refine ⟨226239112881320624893070117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150826075254213749928713411 226239112881320624893070117)
        ·
          refine ⟨42419833665247617167450647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226239112881320624893070117 42419833665247617167450647)
          ·
            refine ⟨63629750497871425751175971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42419833665247617167450647 63629750497871425751175971)
            ·
              refine ⟨95444625746807138626763957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63629750497871425751175971 95444625746807138626763957)
              ·
                refine ⟨8947933663763169246259121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95444625746807138626763957 8947933663763169246259121)
                ·
                  refine ⟨6710950247822376934694341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8947933663763169246259121 6710950247822376934694341)
                  ·
                    refine ⟨1258303171466695675255189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6710950247822376934694341 1258303171466695675255189)
                    ·
                      rfl

theorem cell23_7351610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_7351610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351610 prefixEnd_7351610 := by exact prefixLift 7351610
  have htrace : WordTrace (prefixWord ++ tailWord_7351610) baseStart_7351610 baseEnd_7351610 := by
    simpa [prefixWord, tailWord_7351610, baseEnd_7351610] using wordTrace_append hprefix tailTrace_7351610
  have hstable : (prefixWord ++ tailWord_7351610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351610).length < 2 ^ (prefixWord ++ tailWord_7351610).sum := by decide
  have hdescent : baseEnd_7351610 < baseStart_7351610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351637 : List Nat := [1, 3, 2, 2, 3, 2, 1, 3, 1, 2, 3]
def baseStart_7351637 : Nat := 118140960795 + 7351637 * 2 ^ 59
def prefixEnd_7351637 : Nat := 4983230072969 + 3 ^ 40 * 7351637 * 2
def baseEnd_7351637 : Nat := 3774923378377758420127943

theorem tailTrace_7351637 : CollatzResearch.WordTrace tailWord_7351637 prefixEnd_7351637 3774923378377758420127943 := by
  unfold tailWord_7351637
  simp only [CollatzResearch.WordTrace]
  refine ⟨268136229667282183484501165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178757486444854788989667443 268136229667282183484501165)
  ·
    refine ⟨100551086125230818806687937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268136229667282183484501165 100551086125230818806687937)
    ·
      refine ⟨75413314593923114105015953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100551086125230818806687937 75413314593923114105015953)
      ·
        refine ⟨56559985945442335578761965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75413314593923114105015953 56559985945442335578761965)
        ·
          refine ⟨21209994729540875842035737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56559985945442335578761965 21209994729540875842035737)
          ·
            refine ⟨15907496047155656881526803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21209994729540875842035737 15907496047155656881526803)
            ·
              refine ⟨23861244070733485322290205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15907496047155656881526803 23861244070733485322290205)
              ·
                refine ⟨8947966526525056995858827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23861244070733485322290205 8947966526525056995858827)
                ·
                  refine ⟨13421949789787585493788241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8947966526525056995858827 13421949789787585493788241)
                  ·
                    refine ⟨10066462342340689120341181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13421949789787585493788241 10066462342340689120341181)
                    ·
                      refine ⟨3774923378377758420127943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10066462342340689120341181 3774923378377758420127943)
                      ·
                        rfl

theorem cell23_7351637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_7351637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351637 prefixEnd_7351637 := by exact prefixLift 7351637
  have htrace : WordTrace (prefixWord ++ tailWord_7351637) baseStart_7351637 baseEnd_7351637 := by
    simpa [prefixWord, tailWord_7351637, baseEnd_7351637] using wordTrace_append hprefix tailTrace_7351637
  have hstable : (prefixWord ++ tailWord_7351637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351637).length < 2 ^ (prefixWord ++ tailWord_7351637).sum := by decide
  have hdescent : baseEnd_7351637 < baseStart_7351637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351673 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 2, 3, 4]
def baseStart_7351673 : Nat := 118140960795 + 7351673 * 2 ^ 59
def prefixEnd_7351673 : Nat := 4983230072969 + 3 ^ 40 * 7351673 * 2
def baseEnd_7351673 : Nat := 3774941863681320279277777

theorem tailTrace_7351673 : CollatzResearch.WordTrace tailWord_7351673 prefixEnd_7351673 3774941863681320279277777 := by
  unfold tailWord_7351673
  simp only [CollatzResearch.WordTrace]
  refine ⟨268137542695151761632811673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178758361796767841088541115 268137542695151761632811673)
  ·
    refine ⟨201103157021363821224608755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268137542695151761632811673 201103157021363821224608755)
    ·
      refine ⟨301654735532045731836913133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201103157021363821224608755 301654735532045731836913133)
      ·
        refine ⟨113120525824517149438842425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301654735532045731836913133 113120525824517149438842425)
        ·
          refine ⟨84840394368387862079131819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113120525824517149438842425 84840394368387862079131819)
          ·
            refine ⟨127260591552581793118697729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84840394368387862079131819 127260591552581793118697729)
            ·
              refine ⟨95445443664436344839023297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127260591552581793118697729 95445443664436344839023297)
              ·
                refine ⟨71584082748327258629267473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95445443664436344839023297 71584082748327258629267473)
                ·
                  refine ⟨53688062061245443971950605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71584082748327258629267473 53688062061245443971950605)
                  ·
                    refine ⟨20133023272967041489481477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53688062061245443971950605 20133023272967041489481477)
                    ·
                      refine ⟨3774941863681320279277777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20133023272967041489481477 3774941863681320279277777)
                      ·
                        rfl

theorem cell23_7351673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_7351673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351673 prefixEnd_7351673 := by exact prefixLift 7351673
  have htrace : WordTrace (prefixWord ++ tailWord_7351673) baseStart_7351673 baseEnd_7351673 := by
    simpa [prefixWord, tailWord_7351673, baseEnd_7351673] using wordTrace_append hprefix tailTrace_7351673
  have hstable : (prefixWord ++ tailWord_7351673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351673).length < 2 ^ (prefixWord ++ tailWord_7351673).sum := by decide
  have hdescent : baseEnd_7351673 < baseStart_7351673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351743 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 1, 7]
def baseStart_7351743 : Nat := 118140960795 + 7351743 * 2 ^ 59
def prefixEnd_7351743 : Nat := 4983230072969 + 3 ^ 40 * 7351743 * 2
def baseEnd_7351743 : Nat := 1258325935775711668467485

theorem tailTrace_7351743 : CollatzResearch.WordTrace tailWord_7351743 prefixEnd_7351743 1258325935775711668467485 := by
  unfold tailWord_7351743
  simp only [CollatzResearch.WordTrace]
  refine ⟨268140095804898163587859883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178760063869932109058573255 268140095804898163587859883)
  ·
    refine ⟨402210143707347245381789825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268140095804898163587859883 402210143707347245381789825)
    ·
      refine ⟨301657607780510434036342369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402210143707347245381789825 301657607780510434036342369)
      ·
        refine ⟨226243205835382825527256777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301657607780510434036342369 226243205835382825527256777)
        ·
          refine ⟨169682404376537119145442583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226243205835382825527256777 169682404376537119145442583)
          ·
            refine ⟨254523606564805678718163875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169682404376537119145442583 254523606564805678718163875)
            ·
              refine ⟨381785409847208518077245813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254523606564805678718163875 381785409847208518077245813)
              ·
                refine ⟨35792382173175798569741795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 381785409847208518077245813 35792382173175798569741795)
                ·
                  refine ⟨53688573259763697854612693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35792382173175798569741795 53688573259763697854612693)
                  ·
                    refine ⟨1258325935775711668467485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53688573259763697854612693 1258325935775711668467485)
                    ·
                      rfl

theorem cell23_7351743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_7351743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351743 prefixEnd_7351743 := by exact prefixLift 7351743
  have htrace : WordTrace (prefixWord ++ tailWord_7351743) baseStart_7351743 baseEnd_7351743 := by
    simpa [prefixWord, tailWord_7351743, baseEnd_7351743] using wordTrace_append hprefix tailTrace_7351743
  have hstable : (prefixWord ++ tailWord_7351743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351743).length < 2 ^ (prefixWord ++ tailWord_7351743).sum := by decide
  have hdescent : baseEnd_7351743 < baseStart_7351743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351764 : List Nat := [2, 4, 1, 2, 3, 1, 1, 4, 5]
def baseStart_7351764 : Nat := 118140960795 + 7351764 * 2 ^ 59
def prefixEnd_7351764 : Nat := 4983230072969 + 3 ^ 40 * 7351764 * 2
def baseEnd_7351764 : Nat := 419443176713431047026651

theorem tailTrace_7351764 : CollatzResearch.WordTrace tailWord_7351764 prefixEnd_7351764 419443176713431047026651 := by
  unfold tailWord_7351764
  simp only [CollatzResearch.WordTrace]
  refine ⟨134070430868911042087187173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178760574491881389449582897 134070430868911042087187173)
  ·
    refine ⟨25138205787920820391347595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134070430868911042087187173 25138205787920820391347595)
    ·
      refine ⟨37707308681881230587021393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25138205787920820391347595 37707308681881230587021393)
      ·
        refine ⟨28280481511410922940266045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37707308681881230587021393 28280481511410922940266045)
        ·
          refine ⟨10605180566779096102599767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28280481511410922940266045 10605180566779096102599767)
          ·
            refine ⟨15907770850168644153899651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10605180566779096102599767 15907770850168644153899651)
            ·
              refine ⟨23861656275252966230849477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15907770850168644153899651 23861656275252966230849477)
              ·
                refine ⟨4474060551609931168284277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23861656275252966230849477 4474060551609931168284277)
                ·
                  refine ⟨419443176713431047026651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4474060551609931168284277 419443176713431047026651)
                  ·
                    rfl

theorem cell23_7351764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_7351764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351764 prefixEnd_7351764 := by exact prefixLift 7351764
  have htrace : WordTrace (prefixWord ++ tailWord_7351764) baseStart_7351764 baseEnd_7351764 := by
    simpa [prefixWord, tailWord_7351764, baseEnd_7351764] using wordTrace_append hprefix tailTrace_7351764
  have hstable : (prefixWord ++ tailWord_7351764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351764).length < 2 ^ (prefixWord ++ tailWord_7351764).sum := by decide
  have hdescent : baseEnd_7351764 < baseStart_7351764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351770 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_7351770 : Nat := 118140960795 + 7351770 * 2 ^ 59
def prefixEnd_7351770 : Nat := 4983230072969 + 3 ^ 40 * 7351770 * 2
def baseEnd_7351770 : Nat := 3774991671304806399764831

theorem tailTrace_7351770 : CollatzResearch.WordTrace tailWord_7351770 prefixEnd_7351770 3774991671304806399764831 := by
  unfold tailWord_7351770
  simp only [CollatzResearch.WordTrace]
  refine ⟨67035270143950086799773191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178760720383866898132728509 67035270143950086799773191)
  ·
    refine ⟨100552905215925130199659787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67035270143950086799773191 100552905215925130199659787)
    ·
      refine ⟨150829357823887695299489681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100552905215925130199659787 150829357823887695299489681)
      ·
        refine ⟨113122018367915771474617261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150829357823887695299489681 113122018367915771474617261)
        ·
          refine ⟨42420756887968414302981473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113122018367915771474617261 42420756887968414302981473)
          ·
            refine ⟨31815567665976310727236105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42420756887968414302981473 31815567665976310727236105)
            ·
              refine ⟨23861675749482233045427079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31815567665976310727236105 23861675749482233045427079)
              ·
                refine ⟨35792513624223349568140619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23861675749482233045427079 35792513624223349568140619)
                ·
                  refine ⟨53688770436335024352210929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35792513624223349568140619 53688770436335024352210929)
                  ·
                    refine ⟨40266577827251268264158197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53688770436335024352210929 40266577827251268264158197)
                    ·
                      refine ⟨3774991671304806399764831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40266577827251268264158197 3774991671304806399764831)
                      ·
                        rfl

theorem cell23_7351770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_7351770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351770 prefixEnd_7351770 := by exact prefixLift 7351770
  have htrace : WordTrace (prefixWord ++ tailWord_7351770) baseStart_7351770 baseEnd_7351770 := by
    simpa [prefixWord, tailWord_7351770, baseEnd_7351770] using wordTrace_append hprefix tailTrace_7351770
  have hstable : (prefixWord ++ tailWord_7351770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351770).length < 2 ^ (prefixWord ++ tailWord_7351770).sum := by decide
  have hdescent : baseEnd_7351770 < baseStart_7351770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351780 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_7351780 : Nat := 118140960795 + 7351780 * 2 ^ 59
def prefixEnd_7351780 : Nat := 4983230072969 + 3 ^ 40 * 7351780 * 2
def baseEnd_7351780 : Nat := 3774996806111351360639785

theorem tailTrace_7351780 : CollatzResearch.WordTrace tailWord_7351780 prefixEnd_7351780 3774996806111351360639785 := by
  unfold tailWord_7351780
  simp only [CollatzResearch.WordTrace]
  refine ⟨134070722652882059453478397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178760963537176079271304529 134070722652882059453478397)
  ·
    refine ⟨50276520994830772295054399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134070722652882059453478397 50276520994830772295054399)
    ·
      refine ⟨75414781492246158442581599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50276520994830772295054399 75414781492246158442581599)
      ·
        refine ⟨113122172238369237663872399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75414781492246158442581599 113122172238369237663872399)
        ·
          refine ⟨169683258357553856495808599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113122172238369237663872399 169683258357553856495808599)
          ·
            refine ⟨254524887536330784743712899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169683258357553856495808599 254524887536330784743712899)
            ·
              refine ⟨381787331304496177115569349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254524887536330784743712899 381787331304496177115569349)
              ·
                refine ⟨71585124619593033209169253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381787331304496177115569349 71585124619593033209169253)
                ·
                  refine ⟨13422210866173693726719235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71585124619593033209169253 13422210866173693726719235)
                  ·
                    refine ⟨20133316299260540590078853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13422210866173693726719235 20133316299260540590078853)
                    ·
                      refine ⟨3774996806111351360639785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20133316299260540590078853 3774996806111351360639785)
                      ·
                        rfl

theorem cell23_7351780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_7351780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351780 prefixEnd_7351780 := by exact prefixLift 7351780
  have htrace : WordTrace (prefixWord ++ tailWord_7351780) baseStart_7351780 baseEnd_7351780 := by
    simpa [prefixWord, tailWord_7351780, baseEnd_7351780] using wordTrace_append hprefix tailTrace_7351780
  have hstable : (prefixWord ++ tailWord_7351780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351780).length < 2 ^ (prefixWord ++ tailWord_7351780).sum := by decide
  have hdescent : baseEnd_7351780 < baseStart_7351780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351794 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_7351794 : Nat := 118140960795 + 7351794 * 2 ^ 59
def prefixEnd_7351794 : Nat := 4983230072969 + 3 ^ 40 * 7351794 * 2
def baseEnd_7351794 : Nat := 1258334664946838101954907

theorem tailTrace_7351794 : CollatzResearch.WordTrace tailWord_7351794 prefixEnd_7351794 1258334664946838101954907 := by
  unfold tailWord_7351794
  simp only [CollatzResearch.WordTrace]
  refine ⟨67035488981928349824491609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178761303951808932865310957 67035488981928349824491609)
  ·
    refine ⟨50276616736446262368368707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67035488981928349824491609 50276616736446262368368707)
    ·
      refine ⟨75414925104669393552553061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50276616736446262368368707 75414925104669393552553061)
      ·
        refine ⟨14140298457125511291103699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75414925104669393552553061 14140298457125511291103699)
        ·
          refine ⟨21210447685688266936655549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14140298457125511291103699 21210447685688266936655549)
          ·
            refine ⟨7953917882133100101245831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21210447685688266936655549 7953917882133100101245831)
            ·
              refine ⟨11930876823199650151868747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7953917882133100101245831 11930876823199650151868747)
              ·
                refine ⟨17896315234799475227803121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11930876823199650151868747 17896315234799475227803121)
                ·
                  refine ⟨13422236426099606420852341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17896315234799475227803121 13422236426099606420852341)
                  ·
                    refine ⟨1258334664946838101954907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13422236426099606420852341 1258334664946838101954907)
                    ·
                      rfl

theorem cell23_7351794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_7351794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351794 prefixEnd_7351794 := by exact prefixLift 7351794
  have htrace : WordTrace (prefixWord ++ tailWord_7351794) baseStart_7351794 baseEnd_7351794 := by
    simpa [prefixWord, tailWord_7351794, baseEnd_7351794] using wordTrace_append hprefix tailTrace_7351794
  have hstable : (prefixWord ++ tailWord_7351794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351794).length < 2 ^ (prefixWord ++ tailWord_7351794).sum := by decide
  have hdescent : baseEnd_7351794 < baseStart_7351794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351803 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 10]
def baseStart_7351803 : Nat := 118140960795 + 7351803 * 2 ^ 59
def prefixEnd_7351803 : Nat := 4983230072969 + 3 ^ 40 * 7351803 * 2
def baseEnd_7351803 : Nat := 419445401796267196739131

theorem tailTrace_7351803 : CollatzResearch.WordTrace tailWord_7351803 prefixEnd_7351803 419445401796267196739131 := by
  unfold tailWord_7351803
  simp only [CollatzResearch.WordTrace]
  refine ⟨268142284184680793835044063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178761522789787195890029375 268142284184680793835044063)
  ·
    refine ⟨402213426277021190752566095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268142284184680793835044063 402213426277021190752566095)
    ·
      refine ⟨603320139415531786128849143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402213426277021190752566095 603320139415531786128849143)
      ·
        refine ⟨904980209123297679193273715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603320139415531786128849143 904980209123297679193273715)
        ·
          refine ⟨1357470313684946518789910573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904980209123297679193273715 1357470313684946518789910573)
          ·
            refine ⟨509051367631854944546216465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1357470313684946518789910573 509051367631854944546216465)
            ·
              refine ⟨381788525723891208409662349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509051367631854944546216465 381788525723891208409662349)
              ·
                refine ⟨143170697146459203153623381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 381788525723891208409662349 143170697146459203153623381)
                ·
                  refine ⟨419445401796267196739131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 143170697146459203153623381 419445401796267196739131)
                  ·
                    rfl

theorem cell23_7351803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 10].length) (baseStart_7351803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351803 prefixEnd_7351803 := by exact prefixLift 7351803
  have htrace : WordTrace (prefixWord ++ tailWord_7351803) baseStart_7351803 baseEnd_7351803 := by
    simpa [prefixWord, tailWord_7351803, baseEnd_7351803] using wordTrace_append hprefix tailTrace_7351803
  have hstable : (prefixWord ++ tailWord_7351803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351803).length < 2 ^ (prefixWord ++ tailWord_7351803).sum := by decide
  have hdescent : baseEnd_7351803 < baseStart_7351803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351901 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_7351901 : Nat := 118140960795 + 7351901 * 2 ^ 59
def prefixEnd_7351901 : Nat := 4983230072969 + 3 ^ 40 * 7351901 * 2
def baseEnd_7351901 : Nat := 1258352979090181795742243

theorem tailTrace_7351901 : CollatzResearch.WordTrace tailWord_7351901 prefixEnd_7351901 1258352979090181795742243 := by
  unfold tailWord_7351901
  simp only [CollatzResearch.WordTrace]
  refine ⟨268145858538325756572111557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178763905692217171048074371 268145858538325756572111557)
  ·
    refine ⟨50277348475936079357270917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268145858538325756572111557 50277348475936079357270917)
    ·
      refine ⟨9427002839238014879488297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50277348475936079357270917 9427002839238014879488297)
      ·
        refine ⟨7070252129428511159616223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9427002839238014879488297 7070252129428511159616223)
        ·
          refine ⟨10605378194142766739424335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7070252129428511159616223 10605378194142766739424335)
          ·
            refine ⟨15908067291214150109136503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10605378194142766739424335 15908067291214150109136503)
            ·
              refine ⟨23862100936821225163704755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15908067291214150109136503 23862100936821225163704755)
              ·
                refine ⟨35793151405231837745557133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23862100936821225163704755 35793151405231837745557133)
                ·
                  refine ⟨13422431776961939154583925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35793151405231837745557133 13422431776961939154583925)
                  ·
                    refine ⟨1258352979090181795742243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13422431776961939154583925 1258352979090181795742243)
                    ·
                      rfl

theorem cell23_7351901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_7351901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351901 prefixEnd_7351901 := by exact prefixLift 7351901
  have htrace : WordTrace (prefixWord ++ tailWord_7351901) baseStart_7351901 baseEnd_7351901 := by
    simpa [prefixWord, tailWord_7351901, baseEnd_7351901] using wordTrace_append hprefix tailTrace_7351901
  have hstable : (prefixWord ++ tailWord_7351901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351901).length < 2 ^ (prefixWord ++ tailWord_7351901).sum := by decide
  have hdescent : baseEnd_7351901 < baseStart_7351901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351904 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 5, 2, 2]
def baseStart_7351904 : Nat := 118140960795 + 7351904 * 2 ^ 59
def prefixEnd_7351904 : Nat := 4983230072969 + 3 ^ 40 * 7351904 * 2
def baseEnd_7351904 : Nat := 3775060477712508875489215

theorem tailTrace_7351904 : CollatzResearch.WordTrace tailWord_7351904 prefixEnd_7351904 3775060477712508875489215 := by
  unfold tailWord_7351904
  simp only [CollatzResearch.WordTrace]
  refine ⟨134072983978657444042235383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178763978638209925389647177 134072983978657444042235383)
  ·
    refine ⟨201109475967986166063353075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134072983978657444042235383 201109475967986166063353075)
    ·
      refine ⟨301664213951979249095029613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201109475967986166063353075 301664213951979249095029613)
      ·
        refine ⟨113124080231992218410636105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301664213951979249095029613 113124080231992218410636105)
        ·
          refine ⟨84843060173994163807977079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113124080231992218410636105 84843060173994163807977079)
          ·
            refine ⟨127264590260991245711965619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84843060173994163807977079 127264590260991245711965619)
            ·
              refine ⟨190896885391486868567948429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127264590260991245711965619 190896885391486868567948429)
              ·
                refine ⟨71586332021807575712980661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190896885391486868567948429 71586332021807575712980661)
                ·
                  refine ⟨6711218627044460223091937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71586332021807575712980661 6711218627044460223091937)
                  ·
                    refine ⟨5033413970283345167318953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6711218627044460223091937 5033413970283345167318953)
                    ·
                      refine ⟨3775060477712508875489215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5033413970283345167318953 3775060477712508875489215)
                      ·
                        rfl

theorem cell23_7351904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_7351904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351904 prefixEnd_7351904 := by exact prefixLift 7351904
  have htrace : WordTrace (prefixWord ++ tailWord_7351904) baseStart_7351904 baseEnd_7351904 := by
    simpa [prefixWord, tailWord_7351904, baseEnd_7351904] using wordTrace_append hprefix tailTrace_7351904
  have hstable : (prefixWord ++ tailWord_7351904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351904).length < 2 ^ (prefixWord ++ tailWord_7351904).sum := by decide
  have hdescent : baseEnd_7351904 < baseStart_7351904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351930 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_7351930 : Nat := 118140960795 + 7351930 * 2 ^ 59
def prefixEnd_7351930 : Nat := 4983230072969 + 3 ^ 40 * 7351930 * 2
def baseEnd_7351930 : Nat := 3775073828209525773764095

theorem tailTrace_7351930 : CollatzResearch.WordTrace tailWord_7351930 prefixEnd_7351930 3775073828209525773764095 := by
  unfold tailWord_7351930
  simp only [CollatzResearch.WordTrace]
  refine ⟨67036729063805173631229311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178764610836813796349944829 67036729063805173631229311)
  ·
    refine ⟨100555093595707760446843967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67036729063805173631229311 100555093595707760446843967)
    ·
      refine ⟨150832640393561640670265951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100555093595707760446843967 150832640393561640670265951)
      ·
        refine ⟨226248960590342461005398927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150832640393561640670265951 226248960590342461005398927)
        ·
          refine ⟨339373440885513691508098391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226248960590342461005398927 339373440885513691508098391)
          ·
            refine ⟨509060161328270537262147587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339373440885513691508098391 509060161328270537262147587)
            ·
              refine ⟨763590241992405805893221381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509060161328270537262147587 763590241992405805893221381)
              ·
                refine ⟨143173170373576088604979009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 763590241992405805893221381 143173170373576088604979009)
                ·
                  refine ⟨107379877780182066453734257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143173170373576088604979009 107379877780182066453734257)
                  ·
                    refine ⟨80534908335136549840300693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107379877780182066453734257 80534908335136549840300693)
                    ·
                      refine ⟨3775073828209525773764095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80534908335136549840300693 3775073828209525773764095)
                      ·
                        rfl

theorem cell23_7351930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_7351930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351930 prefixEnd_7351930 := by exact prefixLift 7351930
  have htrace : WordTrace (prefixWord ++ tailWord_7351930) baseStart_7351930 baseEnd_7351930 := by
    simpa [prefixWord, tailWord_7351930, baseEnd_7351930] using wordTrace_append hprefix tailTrace_7351930
  have hstable : (prefixWord ++ tailWord_7351930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351930).length < 2 ^ (prefixWord ++ tailWord_7351930).sum := by decide
  have hdescent : baseEnd_7351930 < baseStart_7351930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352002 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_7352002 : Nat := 118140960795 + 7352002 * 2 ^ 59
def prefixEnd_7352002 : Nat := 4983230072969 + 3 ^ 40 * 7352002 * 2
def baseEnd_7352002 : Nat := 3775110798816649492063765

theorem tailTrace_7352002 : CollatzResearch.WordTrace tailWord_7352002 prefixEnd_7352002 3775110798816649492063765 := by
  unfold tailWord_7352002
  simp only [CollatzResearch.WordTrace]
  refine ⟨67037385577739962705384565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178766361540639900547692173 67037385577739962705384565)
  ·
    refine ⟨6284754897913121503629803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67037385577739962705384565 6284754897913121503629803)
    ·
      refine ⟨9427132346869682255444705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6284754897913121503629803 9427132346869682255444705)
      ·
        refine ⟨7070349260152261691583529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9427132346869682255444705 7070349260152261691583529)
        ·
          refine ⟨5302761945114196268687647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7070349260152261691583529 5302761945114196268687647)
          ·
            refine ⟨7954142917671294403031471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5302761945114196268687647 7954142917671294403031471)
            ·
              refine ⟨11931214376506941604547207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7954142917671294403031471 11931214376506941604547207)
              ·
                refine ⟨17896821564760412406820811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11931214376506941604547207 17896821564760412406820811)
                ·
                  refine ⟨26845232347140618610231217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17896821564760412406820811 26845232347140618610231217)
                  ·
                    refine ⟨20133924260355463957673413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26845232347140618610231217 20133924260355463957673413)
                    ·
                      refine ⟨3775110798816649492063765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20133924260355463957673413 3775110798816649492063765)
                      ·
                        rfl

theorem cell23_7352002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_7352002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352002 prefixEnd_7352002 := by exact prefixLift 7352002
  have htrace : WordTrace (prefixWord ++ tailWord_7352002) baseStart_7352002 baseEnd_7352002 := by
    simpa [prefixWord, tailWord_7352002, baseEnd_7352002] using wordTrace_append hprefix tailTrace_7352002
  have hstable : (prefixWord ++ tailWord_7352002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352002).length < 2 ^ (prefixWord ++ tailWord_7352002).sum := by decide
  have hdescent : baseEnd_7352002 < baseStart_7352002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352007 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_7352007 : Nat := 118140960795 + 7352007 * 2 ^ 59
def prefixEnd_7352007 : Nat := 4983230072969 + 3 ^ 40 * 7352007 * 2
def baseEnd_7352007 : Nat := 3775113366219921972501241

theorem tailTrace_7352007 : CollatzResearch.WordTrace tailWord_7352007 prefixEnd_7352007 3775113366219921972501241 := by
  unfold tailWord_7352007
  simp only [CollatzResearch.WordTrace]
  refine ⟨268149724675941736675470275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178766483117294491116980183 268149724675941736675470275)
  ·
    refine ⟨402224587013912605013205413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268149724675941736675470275 402224587013912605013205413)
    ·
      refine ⟨75417110065108613439976015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 402224587013912605013205413 75417110065108613439976015)
      ·
        refine ⟨113125665097662920159964023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75417110065108613439976015 113125665097662920159964023)
        ·
          refine ⟨169688497646494380239946035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113125665097662920159964023 169688497646494380239946035)
          ·
            refine ⟨254532746469741570359919053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169688497646494380239946035 254532746469741570359919053)
            ·
              refine ⟨95449779926153088884969645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254532746469741570359919053 95449779926153088884969645)
              ·
                refine ⟨35793667472307408331863617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95449779926153088884969645 35793667472307408331863617)
                ·
                  refine ⟨26845250604230556248897713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35793667472307408331863617 26845250604230556248897713)
                  ·
                    refine ⟨20133937953172917186673285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26845250604230556248897713 20133937953172917186673285)
                    ·
                      refine ⟨3775113366219921972501241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20133937953172917186673285 3775113366219921972501241)
                      ·
                        rfl

theorem cell23_7352007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_7352007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352007 prefixEnd_7352007 := by exact prefixLift 7352007
  have htrace : WordTrace (prefixWord ++ tailWord_7352007) baseStart_7352007 baseEnd_7352007 := by
    simpa [prefixWord, tailWord_7352007, baseEnd_7352007] using wordTrace_append hprefix tailTrace_7352007
  have hstable : (prefixWord ++ tailWord_7352007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352007).length < 2 ^ (prefixWord ++ tailWord_7352007).sum := by decide
  have hdescent : baseEnd_7352007 < baseStart_7352007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352011 : List Nat := [1, 1, 1, 1, 3, 2, 1, 7, 2, 2, 2]
def baseStart_7352011 : Nat := 118140960795 + 7352011 * 2 ^ 59
def prefixEnd_7352011 : Nat := 4983230072969 + 3 ^ 40 * 7352011 * 2
def baseEnd_7352011 : Nat := 3775115420142539956851223

theorem tailTrace_7352011 : CollatzResearch.WordTrace tailWord_7352011 prefixEnd_7352011 3775115420142539956851223 := by
  unfold tailWord_7352011
  simp only [CollatzResearch.WordTrace]
  refine ⟨268149870567927245358615887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178766580378618163572410591 268149870567927245358615887)
  ·
    refine ⟨402224805851890868037923831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268149870567927245358615887 402224805851890868037923831)
    ·
      refine ⟨603337208777836302056885747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402224805851890868037923831 603337208777836302056885747)
      ·
        refine ⟨905005813166754453085328621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603337208777836302056885747 905005813166754453085328621)
        ·
          refine ⟨339377179937532919906998233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 905005813166754453085328621 339377179937532919906998233)
          ·
            refine ⟨254532884953149689930248675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339377179937532919906998233 254532884953149689930248675)
            ·
              refine ⟨381799327429724534895373013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254532884953149689930248675 381799327429724534895373013)
              ·
                refine ⟨8948421736634168786610305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 381799327429724534895373013 8948421736634168786610305)
                ·
                  refine ⟨6711316302475626589957729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8948421736634168786610305 6711316302475626589957729)
                  ·
                    refine ⟨5033487226856719942468297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6711316302475626589957729 5033487226856719942468297)
                    ·
                      refine ⟨3775115420142539956851223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5033487226856719942468297 3775115420142539956851223)
                      ·
                        rfl

theorem cell23_7352011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 2, 2].length) (baseStart_7352011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352011 prefixEnd_7352011 := by exact prefixLift 7352011
  have htrace : WordTrace (prefixWord ++ tailWord_7352011) baseStart_7352011 baseEnd_7352011 := by
    simpa [prefixWord, tailWord_7352011, baseEnd_7352011] using wordTrace_append hprefix tailTrace_7352011
  have hstable : (prefixWord ++ tailWord_7352011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352011).length < 2 ^ (prefixWord ++ tailWord_7352011).sum := by decide
  have hdescent : baseEnd_7352011 < baseStart_7352011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352017 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 7]
def baseStart_7352017 : Nat := 118140960795 + 7352017 * 2 ^ 59
def prefixEnd_7352017 : Nat := 4983230072969 + 3 ^ 40 * 7352017 * 2
def baseEnd_7352017 : Nat := 419457611225162992597355

theorem tailTrace_7352017 : CollatzResearch.WordTrace tailWord_7352017 prefixEnd_7352017 419457611225162992597355 := by
  unfold tailWord_7352017
  simp only [CollatzResearch.WordTrace]
  refine ⟨268150089405905508383334305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178766726270603672255556203 268150089405905508383334305)
  ·
    refine ⟨201112567054429131287500729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268150089405905508383334305 201112567054429131287500729)
    ·
      refine ⟨150834425290821848465625547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201112567054429131287500729 150834425290821848465625547)
      ·
        refine ⟨226251637936232772698438321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150834425290821848465625547 226251637936232772698438321)
        ·
          refine ⟨169688728452174579523828741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226251637936232772698438321 169688728452174579523828741)
          ·
            refine ⟨31816636584782733660717889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169688728452174579523828741 31816636584782733660717889)
            ·
              refine ⟨23862477438587050245538417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31816636584782733660717889 23862477438587050245538417)
              ·
                refine ⟨17896858078940287684153813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23862477438587050245538417 17896858078940287684153813)
                ·
                  refine ⟨419457611225162992597355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17896858078940287684153813 419457611225162992597355)
                  ·
                    rfl

theorem cell23_7352017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 7].length) (baseStart_7352017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352017 prefixEnd_7352017 := by exact prefixLift 7352017
  have htrace : WordTrace (prefixWord ++ tailWord_7352017) baseStart_7352017 baseEnd_7352017 := by
    simpa [prefixWord, tailWord_7352017, baseEnd_7352017] using wordTrace_append hprefix tailTrace_7352017
  have hstable : (prefixWord ++ tailWord_7352017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352017).length < 2 ^ (prefixWord ++ tailWord_7352017).sum := by decide
  have hdescent : baseEnd_7352017 < baseStart_7352017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352067 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 4]
def baseStart_7352067 : Nat := 118140960795 + 7352067 * 2 ^ 59
def prefixEnd_7352067 : Nat := 4983230072969 + 3 ^ 40 * 7352067 * 2
def baseEnd_7352067 : Nat := 3775144175059191737750965

theorem tailTrace_7352067 : CollatzResearch.WordTrace tailWord_7352067 prefixEnd_7352067 3775144175059191737750965 := by
  unfold tailWord_7352067
  simp only [CollatzResearch.WordTrace]
  refine ⟨268151913055724366922654455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178767942037149577948436303 268151913055724366922654455)
  ·
    refine ⟨402227869583586550383981683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268151913055724366922654455 402227869583586550383981683)
    ·
      refine ⟨603341804375379825575972525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402227869583586550383981683 603341804375379825575972525)
      ·
        refine ⟨226253176640767434590989697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 603341804375379825575972525 226253176640767434590989697)
        ·
          refine ⟨169689882480575575943242273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226253176640767434590989697 169689882480575575943242273)
          ·
            refine ⟨127267411860431681957431705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169689882480575575943242273 127267411860431681957431705)
            ·
              refine ⟨95450558895323761468073779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127267411860431681957431705 95450558895323761468073779)
              ·
                refine ⟨143175838342985642202110669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95450558895323761468073779 143175838342985642202110669)
                ·
                  refine ⟨53690939378619615825791501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143175838342985642202110669 53690939378619615825791501)
                  ·
                    refine ⟨20134102266982355934671813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53690939378619615825791501 20134102266982355934671813)
                    ·
                      refine ⟨3775144175059191737750965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20134102266982355934671813 3775144175059191737750965)
                      ·
                        rfl

theorem cell23_7352067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_7352067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352067 prefixEnd_7352067 := by exact prefixLift 7352067
  have htrace : WordTrace (prefixWord ++ tailWord_7352067) baseStart_7352067 baseEnd_7352067 := by
    simpa [prefixWord, tailWord_7352067, baseEnd_7352067] using wordTrace_append hprefix tailTrace_7352067
  have hstable : (prefixWord ++ tailWord_7352067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352067).length < 2 ^ (prefixWord ++ tailWord_7352067).sum := by decide
  have hdescent : baseEnd_7352067 < baseStart_7352067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352111 : List Nat := [1, 1, 2, 1, 2, 1, 2, 8, 1, 4]
def baseStart_7352111 : Nat := 118140960795 + 7352111 * 2 ^ 59
def prefixEnd_7352111 : Nat := 4983230072969 + 3 ^ 40 * 7352111 * 2
def baseEnd_7352111 : Nat := 1258388922735996521866921

theorem tailTrace_7352111 : CollatzResearch.WordTrace tailWord_7352111 prefixEnd_7352111 1258388922735996521866921 := by
  unfold tailWord_7352111
  simp only [CollatzResearch.WordTrace]
  refine ⟨268153517867564962437256187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178769011911709974958170791 268153517867564962437256187)
  ·
    refine ⟨402230276801347443655884281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268153517867564962437256187 402230276801347443655884281)
    ·
      refine ⟨301672707601010582741913211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402230276801347443655884281 301672707601010582741913211)
      ·
        refine ⟨452509061401515874112869817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301672707601010582741913211 452509061401515874112869817)
        ·
          refine ⟨339381796051136905584652363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452509061401515874112869817 339381796051136905584652363)
          ·
            refine ⟨509072694076705358376978545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339381796051136905584652363 509072694076705358376978545)
            ·
              refine ⟨381804520557529018782733909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509072694076705358376978545 381804520557529018782733909)
              ·
                refine ⟨4474271725283543188860163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 381804520557529018782733909 4474271725283543188860163)
                ·
                  refine ⟨6711407587925314783290245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4474271725283543188860163 6711407587925314783290245)
                  ·
                    refine ⟨1258388922735996521866921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6711407587925314783290245 1258388922735996521866921)
                    ·
                      rfl

theorem cell23_7352111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 1, 4].length) (baseStart_7352111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352111 prefixEnd_7352111 := by exact prefixLift 7352111
  have htrace : WordTrace (prefixWord ++ tailWord_7352111) baseStart_7352111 baseEnd_7352111 := by
    simpa [prefixWord, tailWord_7352111, baseEnd_7352111] using wordTrace_append hprefix tailTrace_7352111
  have hstable : (prefixWord ++ tailWord_7352111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352111).length < 2 ^ (prefixWord ++ tailWord_7352111).sum := by decide
  have hdescent : baseEnd_7352111 < baseStart_7352111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352118 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_7352118 : Nat := 118140960795 + 7352118 * 2 ^ 59
def prefixEnd_7352118 : Nat := 4983230072969 + 3 ^ 40 * 7352118 * 2
def baseEnd_7352118 : Nat := 3775170362572571038213231

theorem tailTrace_7352118 : CollatzResearch.WordTrace tailWord_7352118 prefixEnd_7352118 3775170362572571038213231 := by
  unfold tailWord_7352118
  simp only [CollatzResearch.WordTrace]
  refine ⟨16759610823658725164547563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178769182119026401755174005 16759610823658725164547563)
  ·
    refine ⟨25139416235488087746821345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16759610823658725164547563 25139416235488087746821345)
    ·
      refine ⟨18854562176616065810116009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25139416235488087746821345 18854562176616065810116009)
      ·
        refine ⟨14140921632462049357587007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18854562176616065810116009 14140921632462049357587007)
        ·
          refine ⟨21211382448693074036380511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14140921632462049357587007 21211382448693074036380511)
          ·
            refine ⟨31817073673039611054570767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21211382448693074036380511 31817073673039611054570767)
            ·
              refine ⟨47725610509559416581856151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31817073673039611054570767 47725610509559416581856151)
              ·
                refine ⟨71588415764339124872784227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47725610509559416581856151 71588415764339124872784227)
                ·
                  refine ⟨107382623646508687309176341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71588415764339124872784227 107382623646508687309176341)
                  ·
                    refine ⟨5033560483430094717617641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107382623646508687309176341 5033560483430094717617641)
                    ·
                      refine ⟨3775170362572571038213231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5033560483430094717617641 3775170362572571038213231)
                      ·
                        rfl

theorem cell23_7352118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_7352118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352118 prefixEnd_7352118 := by exact prefixLift 7352118
  have htrace : WordTrace (prefixWord ++ tailWord_7352118) baseStart_7352118 baseEnd_7352118 := by
    simpa [prefixWord, tailWord_7352118, baseEnd_7352118] using wordTrace_append hprefix tailTrace_7352118
  have hstable : (prefixWord ++ tailWord_7352118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352118).length < 2 ^ (prefixWord ++ tailWord_7352118).sum := by decide
  have hdescent : baseEnd_7352118 < baseStart_7352118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352124 : List Nat := [2, 2, 2, 2, 1, 1, 4, 3, 6]
def baseStart_7352124 : Nat := 118140960795 + 7352124 * 2 ^ 59
def prefixEnd_7352124 : Nat := 4983230072969 + 3 ^ 40 * 7352124 * 2
def baseEnd_7352124 : Nat := 419463715939610890526467

theorem tailTrace_7352124 : CollatzResearch.WordTrace tailWord_7352124 prefixEnd_7352124 419463715939610890526467 := by
  unfold tailWord_7352124
  simp only [CollatzResearch.WordTrace]
  refine ⟨134076996008258932828739713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178769328011011910438319617 134076996008258932828739713)
  ·
    refine ⟨100557747006194199621554785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134076996008258932828739713 100557747006194199621554785)
    ·
      refine ⟨75418310254645649716166089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100557747006194199621554785 75418310254645649716166089)
      ·
        refine ⟨56563732690984237287124567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75418310254645649716166089 56563732690984237287124567)
        ·
          refine ⟨84845599036476355930686851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56563732690984237287124567 84845599036476355930686851)
          ·
            refine ⟨127268398554714533896030277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84845599036476355930686851 127268398554714533896030277)
            ·
              refine ⟨23862824729008975105505677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127268398554714533896030277 23862824729008975105505677)
              ·
                refine ⟨8948559273378365664564629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23862824729008975105505677 8948559273378365664564629)
                ·
                  refine ⟨419463715939610890526467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8948559273378365664564629 419463715939610890526467)
                  ·
                    rfl

theorem cell23_7352124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_7352124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352124 prefixEnd_7352124 := by exact prefixLift 7352124
  have htrace : WordTrace (prefixWord ++ tailWord_7352124) baseStart_7352124 baseEnd_7352124 := by
    simpa [prefixWord, tailWord_7352124, baseEnd_7352124] using wordTrace_append hprefix tailTrace_7352124
  have hstable : (prefixWord ++ tailWord_7352124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352124).length < 2 ^ (prefixWord ++ tailWord_7352124).sum := by decide
  have hdescent : baseEnd_7352124 < baseStart_7352124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352147 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 5]
def baseStart_7352147 : Nat := 118140960795 + 7352147 * 2 ^ 59
def prefixEnd_7352147 : Nat := 4983230072969 + 3 ^ 40 * 7352147 * 2
def baseEnd_7352147 : Nat := 3775185253511551424750597

theorem tailTrace_7352147 : CollatzResearch.WordTrace tailWord_7352147 prefixEnd_7352147 3775185253511551424750597 := by
  unfold tailWord_7352147
  simp only [CollatzResearch.WordTrace]
  refine ⟨268154830895434540585566695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178769887263623027057044463 268154830895434540585566695)
  ·
    refine ⟨402232246343151810878350043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268154830895434540585566695 402232246343151810878350043)
    ·
      refine ⟨603348369514727716317525065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402232246343151810878350043 603348369514727716317525065)
      ·
        refine ⟨452511277136045787238143799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 603348369514727716317525065 452511277136045787238143799)
        ·
          refine ⟨678766915704068680857215699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452511277136045787238143799 678766915704068680857215699)
          ·
            refine ⟨1018150373556103021285823549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678766915704068680857215699 1018150373556103021285823549)
            ·
              refine ⟨381806390083538632982183831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1018150373556103021285823549 381806390083538632982183831)
              ·
                refine ⟨572709585125307949473275747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381806390083538632982183831 572709585125307949473275747)
                ·
                  refine ⟨859064377687961924209913621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572709585125307949473275747 859064377687961924209913621)
                  ·
                    refine ⟨40268642704123215197339701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 859064377687961924209913621 40268642704123215197339701)
                    ·
                      refine ⟨3775185253511551424750597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40268642704123215197339701 3775185253511551424750597)
                      ·
                        rfl

theorem cell23_7352147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_7352147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352147 prefixEnd_7352147 := by exact prefixLift 7352147
  have htrace : WordTrace (prefixWord ++ tailWord_7352147) baseStart_7352147 baseEnd_7352147 := by
    simpa [prefixWord, tailWord_7352147, baseEnd_7352147] using wordTrace_append hprefix tailTrace_7352147
  have hstable : (prefixWord ++ tailWord_7352147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352147).length < 2 ^ (prefixWord ++ tailWord_7352147).sum := by decide
  have hdescent : baseEnd_7352147 < baseStart_7352147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352161 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 4, 3, 2]
def baseStart_7352161 : Nat := 118140960795 + 7352161 * 2 ^ 59
def prefixEnd_7352161 : Nat := 4983230072969 + 3 ^ 40 * 7352161 * 2
def baseEnd_7352161 : Nat := 3775192442240714369975533

theorem tailTrace_7352161 : CollatzResearch.WordTrace tailWord_7352161 prefixEnd_7352161 3775192442240714369975533 := by
  unfold tailWord_7352161
  simp only [CollatzResearch.WordTrace]
  refine ⟨268155341517383820976576337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178770227678255880651050891 268155341517383820976576337)
  ·
    refine ⟨201116506138037865732432253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268155341517383820976576337 201116506138037865732432253)
    ·
      refine ⟨75418689801764199649662095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201116506138037865732432253 75418689801764199649662095)
      ·
        refine ⟨113128034702646299474493143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75418689801764199649662095 113128034702646299474493143)
        ·
          refine ⟨169692052053969449211739715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113128034702646299474493143 169692052053969449211739715)
          ·
            refine ⟨254538078080954173817609573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169692052053969449211739715 254538078080954173817609573)
            ·
              refine ⟨47725889640178907590801795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254538078080954173817609573 47725889640178907590801795)
              ·
                refine ⟨71588834460268361386202693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47725889640178907590801795 71588834460268361386202693)
                ·
                  refine ⟨13422906461300317759913005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71588834460268361386202693 13422906461300317759913005)
                  ·
                    refine ⟨5033589922987619159967377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13422906461300317759913005 5033589922987619159967377)
                    ·
                      refine ⟨3775192442240714369975533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5033589922987619159967377 3775192442240714369975533)
                      ·
                        rfl

theorem cell23_7352161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_7352161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352161 prefixEnd_7352161 := by exact prefixLift 7352161
  have htrace : WordTrace (prefixWord ++ tailWord_7352161) baseStart_7352161 baseEnd_7352161 := by
    simpa [prefixWord, tailWord_7352161, baseEnd_7352161] using wordTrace_append hprefix tailTrace_7352161
  have hstable : (prefixWord ++ tailWord_7352161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352161).length < 2 ^ (prefixWord ++ tailWord_7352161).sum := by decide
  have hdescent : baseEnd_7352161 < baseStart_7352161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352168 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_7352168 : Nat := 118140960795 + 7352168 * 2 ^ 59
def prefixEnd_7352168 : Nat := 4983230072969 + 3 ^ 40 * 7352168 * 2
def baseEnd_7352168 : Nat := 3775196036605295842588001

theorem tailTrace_7352168 : CollatzResearch.WordTrace tailWord_7352168 prefixEnd_7352168 3775196036605295842588001 := by
  unfold tailWord_7352168
  simp only [CollatzResearch.WordTrace]
  refine ⟨134077798414179230586040579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178770397885572307448054105 134077798414179230586040579)
  ·
    refine ⟨201116697621268845879060869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134077798414179230586040579 201116697621268845879060869)
    ·
      refine ⟨37709380803987908602323913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201116697621268845879060869 37709380803987908602323913)
      ·
        refine ⟨28282035602990931451742935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37709380803987908602323913 28282035602990931451742935)
        ·
          refine ⟨42423053404486397177614403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28282035602990931451742935 42423053404486397177614403)
          ·
            refine ⟨63634580106729595766421605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42423053404486397177614403 63634580106729595766421605)
            ·
              refine ⟨11931483770011799206204051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63634580106729595766421605 11931483770011799206204051)
              ·
                refine ⟨17897225655017698809306077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11931483770011799206204051 17897225655017698809306077)
                ·
                  refine ⟨6711459620631637053489779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17897225655017698809306077 6711459620631637053489779)
                  ·
                    refine ⟨10067189430947455580234669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6711459620631637053489779 10067189430947455580234669)
                    ·
                      refine ⟨3775196036605295842588001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10067189430947455580234669 3775196036605295842588001)
                      ·
                        rfl

theorem cell23_7352168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_7352168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352168 prefixEnd_7352168 := by exact prefixLift 7352168
  have htrace : WordTrace (prefixWord ++ tailWord_7352168) baseStart_7352168 baseEnd_7352168 := by
    simpa [prefixWord, tailWord_7352168, baseEnd_7352168] using wordTrace_append hprefix tailTrace_7352168
  have hstable : (prefixWord ++ tailWord_7352168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352168).length < 2 ^ (prefixWord ++ tailWord_7352168).sum := by decide
  have hdescent : baseEnd_7352168 < baseStart_7352168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352204 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_7352204 : Nat := 118140960795 + 7352204 * 2 ^ 59
def prefixEnd_7352204 : Nat := 4983230072969 + 3 ^ 40 * 7352204 * 2
def baseEnd_7352204 : Nat := 3775214521908857701737835

theorem tailTrace_7352204 : CollatzResearch.WordTrace tailWord_7352204 prefixEnd_7352204 3775214521908857701737835 := by
  unfold tailWord_7352204
  simp only [CollatzResearch.WordTrace]
  refine ⟨134078454928114019660195833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178771273237485359546927777 134078454928114019660195833)
  ·
    refine ⟨100558841196085514745146875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134078454928114019660195833 100558841196085514745146875)
    ·
      refine ⟨150838261794128272117720313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100558841196085514745146875 150838261794128272117720313)
      ·
        refine ⟨113128696345596204088290235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150838261794128272117720313 113128696345596204088290235)
        ·
          refine ⟨169693044518394306132435353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113128696345596204088290235 169693044518394306132435353)
          ·
            refine ⟨127269783388795729599326515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169693044518394306132435353 127269783388795729599326515)
            ·
              refine ⟨190904675083193594398989773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127269783388795729599326515 190904675083193594398989773)
              ·
                refine ⟨71589253156197597899621165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190904675083193594398989773 71589253156197597899621165)
                ·
                  refine ⟨26845969933574099212357937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71589253156197597899621165 26845969933574099212357937)
                  ·
                    refine ⟨20134477450180574409268453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26845969933574099212357937 20134477450180574409268453)
                    ·
                      refine ⟨3775214521908857701737835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20134477450180574409268453 3775214521908857701737835)
                      ·
                        rfl

theorem cell23_7352204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_7352204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352204 prefixEnd_7352204 := by exact prefixLift 7352204
  have htrace : WordTrace (prefixWord ++ tailWord_7352204) baseStart_7352204 baseEnd_7352204 := by
    simpa [prefixWord, tailWord_7352204, baseEnd_7352204] using wordTrace_append hprefix tailTrace_7352204
  have hstable : (prefixWord ++ tailWord_7352204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352204).length < 2 ^ (prefixWord ++ tailWord_7352204).sum := by decide
  have hdescent : baseEnd_7352204 < baseStart_7352204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352231 : List Nat := [1, 1, 6, 1, 2, 2, 2, 8]
def baseStart_7352231 : Nat := 118140960795 + 7352231 * 2 ^ 59
def prefixEnd_7352231 : Nat := 4983230072969 + 3 ^ 40 * 7352231 * 2
def baseEnd_7352231 : Nat := 139823273551352929485193

theorem tailTrace_7352231 : CollatzResearch.WordTrace tailWord_7352231 prefixEnd_7352231 139823273551352929485193 := by
  unfold tailWord_7352231
  simp only [CollatzResearch.WordTrace]
  refine ⟨268157894627130222931624547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178771929751420148621083031 268157894627130222931624547)
  ·
    refine ⟨402236841940695334397436821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268157894627130222931624547 402236841940695334397436821)
    ·
      refine ⟨18854851965970093799879851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 402236841940695334397436821 18854851965970093799879851)
      ·
        refine ⟨28282277948955140699819777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18854851965970093799879851 28282277948955140699819777)
        ·
          refine ⟨21211708461716355524864833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28282277948955140699819777 21211708461716355524864833)
          ·
            refine ⟨15908781346287266643648625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21211708461716355524864833 15908781346287266643648625)
            ·
              refine ⟨11931586009715449982736469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15908781346287266643648625 11931586009715449982736469)
              ·
                refine ⟨139823273551352929485193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11931586009715449982736469 139823273551352929485193)
                ·
                  rfl

theorem cell23_7352231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 8].length) (baseStart_7352231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352231 prefixEnd_7352231 := by exact prefixLift 7352231
  have htrace : WordTrace (prefixWord ++ tailWord_7352231) baseStart_7352231 baseEnd_7352231 := by
    simpa [prefixWord, tailWord_7352231, baseEnd_7352231] using wordTrace_append hprefix tailTrace_7352231
  have hstable : (prefixWord ++ tailWord_7352231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352231).length < 2 ^ (prefixWord ++ tailWord_7352231).sum := by decide
  have hdescent : baseEnd_7352231 < baseStart_7352231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352245 : List Nat := [1, 3, 3, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_7352245 : Nat := 118140960795 + 7352245 * 2 ^ 59
def prefixEnd_7352245 : Nat := 4983230072969 + 3 ^ 40 * 7352245 * 2
def baseEnd_7352245 : Nat := 3775235574615692041325147

theorem tailTrace_7352245 : CollatzResearch.WordTrace tailWord_7352245 prefixEnd_7352245 3775235574615692041325147 := by
  unfold tailWord_7352245
  simp only [CollatzResearch.WordTrace]
  refine ⟨268158405249079503322634189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178772270166053002215089459 268158405249079503322634189)
  ·
    refine ⟨100559401968404813745987821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268158405249079503322634189 100559401968404813745987821)
    ·
      refine ⟨37709775738151805154745433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100559401968404813745987821 37709775738151805154745433)
      ·
        refine ⟨28282331803613853866059075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37709775738151805154745433 28282331803613853866059075)
        ·
          refine ⟨42423497705420780799088613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28282331803613853866059075 42423497705420780799088613)
          ·
            refine ⟨7954405819766396399829115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42423497705420780799088613 7954405819766396399829115)
            ·
              refine ⟨11931608729649594599743673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7954405819766396399829115 11931608729649594599743673)
              ·
                refine ⟨8948706547237195949807755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11931608729649594599743673 8948706547237195949807755)
                ·
                  refine ⟨13423059820855793924711633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8948706547237195949807755 13423059820855793924711633)
                  ·
                    refine ⟨10067294865641845443533725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13423059820855793924711633 10067294865641845443533725)
                    ·
                      refine ⟨3775235574615692041325147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10067294865641845443533725 3775235574615692041325147)
                      ·
                        rfl

theorem cell23_7352245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_7352245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352245 prefixEnd_7352245 := by exact prefixLift 7352245
  have htrace : WordTrace (prefixWord ++ tailWord_7352245) baseStart_7352245 baseEnd_7352245 := by
    simpa [prefixWord, tailWord_7352245, baseEnd_7352245] using wordTrace_append hprefix tailTrace_7352245
  have hstable : (prefixWord ++ tailWord_7352245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352245).length < 2 ^ (prefixWord ++ tailWord_7352245).sum := by decide
  have hdescent : baseEnd_7352245 < baseStart_7352245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352291 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 2, 6]
def baseStart_7352291 : Nat := 118140960795 + 7352291 * 2 ^ 59
def prefixEnd_7352291 : Nat := 4983230072969 + 3 ^ 40 * 7352291 * 2
def baseEnd_7352291 : Nat := 1258419731575266287116645

theorem tailTrace_7352291 : CollatzResearch.WordTrace tailWord_7352291 prefixEnd_7352291 1258419731575266287116645 := by
  unfold tailWord_7352291
  simp only [CollatzResearch.WordTrace]
  refine ⟨268160083006912853178808727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178773388671275235452539151 268160083006912853178808727)
  ·
    refine ⟨402240124510369279768213091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268160083006912853178808727 402240124510369279768213091)
    ·
      refine ⟨603360186765553919652319637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402240124510369279768213091 603360186765553919652319637)
      ·
        refine ⟨28282508754635339983702483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 603360186765553919652319637 28282508754635339983702483)
        ·
          refine ⟨42423763131953009975553725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28282508754635339983702483 42423763131953009975553725)
          ·
            refine ⟨15908911174482378740832647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42423763131953009975553725 15908911174482378740832647)
            ·
              refine ⟨23863366761723568111248971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15908911174482378740832647 23863366761723568111248971)
              ·
                refine ⟨35795050142585352166873457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23863366761723568111248971 35795050142585352166873457)
                ·
                  refine ⟨26846287606939014125155093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35795050142585352166873457 26846287606939014125155093)
                  ·
                    refine ⟨1258419731575266287116645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26846287606939014125155093 1258419731575266287116645)
                    ·
                      rfl

theorem cell23_7352291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 6].length) (baseStart_7352291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352291 prefixEnd_7352291 := by exact prefixLift 7352291
  have htrace : WordTrace (prefixWord ++ tailWord_7352291) baseStart_7352291 baseEnd_7352291 := by
    simpa [prefixWord, tailWord_7352291, baseEnd_7352291] using wordTrace_append hprefix tailTrace_7352291
  have hstable : (prefixWord ++ tailWord_7352291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352291).length < 2 ^ (prefixWord ++ tailWord_7352291).sum := by decide
  have hdescent : baseEnd_7352291 < baseStart_7352291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352304 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 9]
def baseStart_7352304 : Nat := 118140960795 + 7352304 * 2 ^ 59
def prefixEnd_7352304 : Nat := 4983230072969 + 3 ^ 40 * 7352304 * 2
def baseEnd_7352304 : Nat := 419473985552700812276375

theorem tailTrace_7352304 : CollatzResearch.WordTrace tailWord_7352304 prefixEnd_7352304 419473985552700812276375 := by
  unfold tailWord_7352304
  simp only [CollatzResearch.WordTrace]
  refine ⟨134080278577932878199515983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178773704770577170932687977 134080278577932878199515983)
  ·
    refine ⟨201120417866899317299273975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134080278577932878199515983 201120417866899317299273975)
    ·
      refine ⟨301680626800348975948910963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201120417866899317299273975 301680626800348975948910963)
      ·
        refine ⟨452520940200523463923366445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301680626800348975948910963 452520940200523463923366445)
        ·
          refine ⟨169695352575196298971262417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 452520940200523463923366445 169695352575196298971262417)
          ·
            refine ⟨127271514431397224228446813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169695352575196298971262417 127271514431397224228446813)
            ·
              refine ⟨47726817911773959085667555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127271514431397224228446813 47726817911773959085667555)
              ·
                refine ⟨71590226867660938628501333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47726817911773959085667555 71590226867660938628501333)
                ·
                  refine ⟨419473985552700812276375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71590226867660938628501333 419473985552700812276375)
                  ·
                    rfl

theorem cell23_7352304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 9].length) (baseStart_7352304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352304 prefixEnd_7352304 := by exact prefixLift 7352304
  have htrace : WordTrace (prefixWord ++ tailWord_7352304) baseStart_7352304 baseEnd_7352304 := by
    simpa [prefixWord, tailWord_7352304, baseEnd_7352304] using wordTrace_append hprefix tailTrace_7352304
  have hstable : (prefixWord ++ tailWord_7352304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352304).length < 2 ^ (prefixWord ++ tailWord_7352304).sum := by decide
  have hdescent : baseEnd_7352304 < baseStart_7352304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352314 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_7352314 : Nat := 118140960795 + 7352314 * 2 ^ 59
def prefixEnd_7352314 : Nat := 4983230072969 + 3 ^ 40 * 7352314 * 2
def baseEnd_7352314 : Nat := 3775271004780852271362329

theorem tailTrace_7352314 : CollatzResearch.WordTrace tailWord_7352314 prefixEnd_7352314 3775271004780852271362329 := by
  unfold tailWord_7352314
  simp only [CollatzResearch.WordTrace]
  refine ⟨67040230471457382026723999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178773947923886352071263997 67040230471457382026723999)
  ·
    refine ⟨100560345707186073040085999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67040230471457382026723999 100560345707186073040085999)
    ·
      refine ⟨150840518560779109560128999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100560345707186073040085999 150840518560779109560128999)
      ·
        refine ⟨226260777841168664340193499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150840518560779109560128999 226260777841168664340193499)
        ·
          refine ⟨339391166761752996510290249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226260777841168664340193499 339391166761752996510290249)
          ·
            refine ⟨254543375071314747382717687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339391166761752996510290249 254543375071314747382717687)
            ·
              refine ⟨381815062606972121074076531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254543375071314747382717687 381815062606972121074076531)
              ·
                refine ⟨572722593910458181611114797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381815062606972121074076531 572722593910458181611114797)
                ·
                  refine ⟨214770972716421818104168049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 572722593910458181611114797 214770972716421818104168049)
                  ·
                    refine ⟨161078229537316363578126037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 214770972716421818104168049 161078229537316363578126037)
                    ·
                      refine ⟨3775271004780852271362329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161078229537316363578126037 3775271004780852271362329)
                      ·
                        rfl

theorem cell23_7352314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_7352314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352314 prefixEnd_7352314 := by exact prefixLift 7352314
  have htrace : WordTrace (prefixWord ++ tailWord_7352314) baseStart_7352314 baseEnd_7352314 := by
    simpa [prefixWord, tailWord_7352314, baseEnd_7352314] using wordTrace_append hprefix tailTrace_7352314
  have hstable : (prefixWord ++ tailWord_7352314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352314).length < 2 ^ (prefixWord ++ tailWord_7352314).sum := by decide
  have hdescent : baseEnd_7352314 < baseStart_7352314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352326 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_7352326 : Nat := 118140960795 + 7352326 * 2 ^ 59
def prefixEnd_7352326 : Nat := 4983230072969 + 3 ^ 40 * 7352326 * 2
def baseEnd_7352326 : Nat := 3775277166548706224412275

theorem tailTrace_7352326 : CollatzResearch.WordTrace tailWord_7352326 prefixEnd_7352326 3775277166548706224412275 := by
  unfold tailWord_7352326
  simp only [CollatzResearch.WordTrace]
  refine ⟨8380042486305814192385401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178774239707857369437555221 8380042486305814192385401)
  ·
    refine ⟨6285031864729360644289051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8380042486305814192385401 6285031864729360644289051)
    ·
      refine ⟨9427547797094040966433577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6285031864729360644289051 9427547797094040966433577)
      ·
        refine ⟨7070660847820530724825183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9427547797094040966433577 7070660847820530724825183)
        ·
          refine ⟨10605991271730796087237775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7070660847820530724825183 10605991271730796087237775)
          ·
            refine ⟨15908986907596194130856663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10605991271730796087237775 15908986907596194130856663)
            ·
              refine ⟨23863480361394291196284995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15908986907596194130856663 23863480361394291196284995)
              ·
                refine ⟨35795220542091436794427493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23863480361394291196284995 35795220542091436794427493)
                ·
                  refine ⟨6711603851642144398955155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35795220542091436794427493 6711603851642144398955155)
                  ·
                    refine ⟨10067405777463216598432733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6711603851642144398955155 10067405777463216598432733)
                    ·
                      refine ⟨3775277166548706224412275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10067405777463216598432733 3775277166548706224412275)
                      ·
                        rfl

theorem cell23_7352326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_7352326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352326 prefixEnd_7352326 := by exact prefixLift 7352326
  have htrace : WordTrace (prefixWord ++ tailWord_7352326) baseStart_7352326 baseEnd_7352326 := by
    simpa [prefixWord, tailWord_7352326, baseEnd_7352326] using wordTrace_append hprefix tailTrace_7352326
  have hstable : (prefixWord ++ tailWord_7352326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352326).length < 2 ^ (prefixWord ++ tailWord_7352326).sum := by decide
  have hdescent : baseEnd_7352326 < baseStart_7352326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352331 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 3]
def baseStart_7352331 : Nat := 118140960795 + 7352331 * 2 ^ 59
def prefixEnd_7352331 : Nat := 4983230072969 + 3 ^ 40 * 7352331 * 2
def baseEnd_7352331 : Nat := 3775279733951978704849751

theorem tailTrace_7352331 : CollatzResearch.WordTrace tailWord_7352331 prefixEnd_7352331 3775279733951978704849751 := by
  unfold tailWord_7352331
  simp only [CollatzResearch.WordTrace]
  refine ⟨268161541926767940010264847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178774361284511960006843231 268161541926767940010264847)
  ·
    refine ⟨402242312890151910015397271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268161541926767940010264847 402242312890151910015397271)
    ·
      refine ⟨603363469335227865023095907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402242312890151910015397271 603363469335227865023095907)
      ·
        refine ⟨905045204002841797534643861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603363469335227865023095907 905045204002841797534643861)
        ·
          refine ⟨42423993937633209259436431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 905045204002841797534643861 42423993937633209259436431)
          ·
            refine ⟨63635990906449813889154647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42423993937633209259436431 63635990906449813889154647)
            ·
              refine ⟨95453986359674720833731971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63635990906449813889154647 95453986359674720833731971)
              ·
                refine ⟨143180979539512081250597957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95453986359674720833731971 143180979539512081250597957)
                ·
                  refine ⟨26846433663658515234487117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143180979539512081250597957 26846433663658515234487117)
                  ·
                    refine ⟨10067412623871943212932669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26846433663658515234487117 10067412623871943212932669)
                    ·
                      refine ⟨3775279733951978704849751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10067412623871943212932669 3775279733951978704849751)
                      ·
                        rfl

theorem cell23_7352331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 3].length) (baseStart_7352331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352331 prefixEnd_7352331 := by exact prefixLift 7352331
  have htrace : WordTrace (prefixWord ++ tailWord_7352331) baseStart_7352331 baseEnd_7352331 := by
    simpa [prefixWord, tailWord_7352331, baseEnd_7352331] using wordTrace_append hprefix tailTrace_7352331
  have hstable : (prefixWord ++ tailWord_7352331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352331).length < 2 ^ (prefixWord ++ tailWord_7352331).sum := by decide
  have hdescent : baseEnd_7352331 < baseStart_7352331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352348 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_7352348 : Nat := 118140960795 + 7352348 * 2 ^ 59
def prefixEnd_7352348 : Nat := 4983230072969 + 3 ^ 40 * 7352348 * 2
def baseEnd_7352348 : Nat := 3775288463123105138337173

theorem tailTrace_7352348 : CollatzResearch.WordTrace tailWord_7352348 prefixEnd_7352348 3775288463123105138337173 := by
  unfold tailWord_7352348
  simp only [CollatzResearch.WordTrace]
  refine ⟨134081080983853175956816849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178774774645137567942422465 134081080983853175956816849)
  ·
    refine ⟨100560810737889881967612637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134081080983853175956816849 100560810737889881967612637)
    ·
      refine ⟨37710304026708705737854739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100560810737889881967612637 37710304026708705737854739)
      ·
        refine ⟨56565456040063058606782109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37710304026708705737854739 56565456040063058606782109)
        ·
          refine ⟨21212046015023646977543291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56565456040063058606782109 21212046015023646977543291)
          ·
            refine ⟨31818069022535470466314937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21212046015023646977543291 31818069022535470466314937)
            ·
              refine ⟨23863551766901602849736203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31818069022535470466314937 23863551766901602849736203)
              ·
                refine ⟨35795327650352404274604305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23863551766901602849736203 35795327650352404274604305)
                ·
                  refine ⟨26846495737764303205953229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35795327650352404274604305 26846495737764303205953229)
                  ·
                    refine ⟨10067435901661613702232461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26846495737764303205953229 10067435901661613702232461)
                    ·
                      refine ⟨3775288463123105138337173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10067435901661613702232461 3775288463123105138337173)
                      ·
                        rfl

theorem cell23_7352348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_7352348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352348 prefixEnd_7352348 := by exact prefixLift 7352348
  have htrace : WordTrace (prefixWord ++ tailWord_7352348) baseStart_7352348 baseEnd_7352348 := by
    simpa [prefixWord, tailWord_7352348, baseEnd_7352348] using wordTrace_append hprefix tailTrace_7352348
  have hstable : (prefixWord ++ tailWord_7352348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352348).length < 2 ^ (prefixWord ++ tailWord_7352348).sum := by decide
  have hdescent : baseEnd_7352348 < baseStart_7352348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352349 : List Nat := [1, 4, 2, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_7352349 : Nat := 118140960795 + 7352349 * 2 ^ 59
def prefixEnd_7352349 : Nat := 4983230072969 + 3 ^ 40 * 7352349 * 2
def baseEnd_7352349 : Nat := 3775288976603759634424669

theorem tailTrace_7352349 : CollatzResearch.WordTrace tailWord_7352349 prefixEnd_7352349 3775288976603759634424669 := by
  unfold tailWord_7352349
  simp only [CollatzResearch.WordTrace]
  refine ⟨268162198440702729084420101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178774798960468486056280067 268162198440702729084420101)
  ·
    refine ⟨50280412207631761703328769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268162198440702729084420101 50280412207631761703328769)
    ·
      refine ⟨37710309155723821277496577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50280412207631761703328769 37710309155723821277496577)
      ·
        refine ⟨28282731866792865958122433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37710309155723821277496577 28282731866792865958122433)
        ·
          refine ⟨21212048900094649468591825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28282731866792865958122433 21212048900094649468591825)
          ·
            refine ⟨15909036675070987101443869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21212048900094649468591825 15909036675070987101443869)
            ·
              refine ⟨5965888753151620163041451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15909036675070987101443869 5965888753151620163041451)
              ·
                refine ⟨8948833129727430244562177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5965888753151620163041451 8948833129727430244562177)
                ·
                  refine ⟨6711624847295572683421633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8948833129727430244562177 6711624847295572683421633)
                  ·
                    refine ⟨5033718635471679512566225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6711624847295572683421633 5033718635471679512566225)
                    ·
                      refine ⟨3775288976603759634424669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5033718635471679512566225 3775288976603759634424669)
                      ·
                        rfl

theorem cell23_7352349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_7352349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352349 prefixEnd_7352349 := by exact prefixLift 7352349
  have htrace : WordTrace (prefixWord ++ tailWord_7352349) baseStart_7352349 baseEnd_7352349 := by
    simpa [prefixWord, tailWord_7352349, baseEnd_7352349] using wordTrace_append hprefix tailTrace_7352349
  have hstable : (prefixWord ++ tailWord_7352349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352349).length < 2 ^ (prefixWord ++ tailWord_7352349).sum := by decide
  have hdescent : baseEnd_7352349 < baseStart_7352349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352371 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 4]
def baseStart_7352371 : Nat := 118140960795 + 7352371 * 2 ^ 59
def prefixEnd_7352371 : Nat := 4983230072969 + 3 ^ 40 * 7352371 * 2
def baseEnd_7352371 : Nat := 3775300273178158548349567

theorem tailTrace_7352371 : CollatzResearch.WordTrace tailWord_7352371 prefixEnd_7352371 3775300273178158548349567 := by
  unfold tailWord_7352371
  simp only [CollatzResearch.WordTrace]
  refine ⟨268163000846623026841720967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178775333897748684561147311 268163000846623026841720967)
  ·
    refine ⟨402244501269934540262581451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268163000846623026841720967 402244501269934540262581451)
    ·
      refine ⟨603366751904901810393872177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402244501269934540262581451 603366751904901810393872177)
      ·
        refine ⟨452525063928676357795404133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 603366751904901810393872177 452525063928676357795404133)
        ·
          refine ⟨84848449486626817086638275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 452525063928676357795404133 84848449486626817086638275)
          ·
            refine ⟨127272674229940225629957413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84848449486626817086638275 127272674229940225629957413)
            ·
              refine ⟨23863626418113792305617015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127272674229940225629957413 23863626418113792305617015)
              ·
                refine ⟨35795439627170688458425523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23863626418113792305617015 35795439627170688458425523)
                ·
                  refine ⟨53693159440756032687638285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35795439627170688458425523 53693159440756032687638285)
                  ·
                    refine ⟨20134934790283512257864357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53693159440756032687638285 20134934790283512257864357)
                    ·
                      refine ⟨3775300273178158548349567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20134934790283512257864357 3775300273178158548349567)
                      ·
                        rfl

theorem cell23_7352371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_7352371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352371 prefixEnd_7352371 := by exact prefixLift 7352371
  have htrace : WordTrace (prefixWord ++ tailWord_7352371) baseStart_7352371 baseEnd_7352371 := by
    simpa [prefixWord, tailWord_7352371, baseEnd_7352371] using wordTrace_append hprefix tailTrace_7352371
  have hstable : (prefixWord ++ tailWord_7352371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352371).length < 2 ^ (prefixWord ++ tailWord_7352371).sum := by decide
  have hdescent : baseEnd_7352371 < baseStart_7352371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352448 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 3, 5, 2]
def baseStart_7352448 : Nat := 118140960795 + 7352448 * 2 ^ 59
def prefixEnd_7352448 : Nat := 4983230072969 + 3 ^ 40 * 7352448 * 2
def baseEnd_7352448 : Nat := 3775339811188554747086713

theorem tailTrace_7352448 : CollatzResearch.WordTrace tailWord_7352448 prefixEnd_7352448 3775339811188554747086713 := by
  unfold tailWord_7352448
  simp only [CollatzResearch.WordTrace]
  refine ⟨134082904633672034496136999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178777206178229379328182665 134082904633672034496136999)
  ·
    refine ⟨201124356950508051744205499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134082904633672034496136999 201124356950508051744205499)
    ·
      refine ⟨301686535425762077616308249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201124356950508051744205499 301686535425762077616308249)
      ·
        refine ⟨226264901569321558212231187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301686535425762077616308249 226264901569321558212231187)
        ·
          refine ⟨339397352353982337318346781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226264901569321558212231187 339397352353982337318346781)
          ·
            refine ⟨127274007132743376494380043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339397352353982337318346781 127274007132743376494380043)
            ·
              refine ⟨190911010699115064741570065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127274007132743376494380043 190911010699115064741570065)
              ·
                refine ⟨143183258024336298556177549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190911010699115064741570065 143183258024336298556177549)
                ·
                  refine ⟨53693721759126111958566581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143183258024336298556177549 53693721759126111958566581)
                  ·
                    refine ⟨5033786414918072996115617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53693721759126111958566581 5033786414918072996115617)
                    ·
                      refine ⟨3775339811188554747086713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5033786414918072996115617 3775339811188554747086713)
                      ·
                        rfl

theorem cell23_7352448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 5, 2].length) (baseStart_7352448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352448 prefixEnd_7352448 := by exact prefixLift 7352448
  have htrace : WordTrace (prefixWord ++ tailWord_7352448) baseStart_7352448 baseEnd_7352448 := by
    simpa [prefixWord, tailWord_7352448, baseEnd_7352448] using wordTrace_append hprefix tailTrace_7352448
  have hstable : (prefixWord ++ tailWord_7352448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352448).length < 2 ^ (prefixWord ++ tailWord_7352448).sum := by decide
  have hdescent : baseEnd_7352448 < baseStart_7352448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352458 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 3, 5]
def baseStart_7352458 : Nat := 118140960795 + 7352458 * 2 ^ 59
def prefixEnd_7352458 : Nat := 4983230072969 + 3 ^ 40 * 7352458 * 2
def baseEnd_7352458 : Nat := 1258448315331699902653889

theorem tailTrace_7352458 : CollatzResearch.WordTrace tailWord_7352458 prefixEnd_7352458 1258448315331699902653889 := by
  unfold tailWord_7352458
  simp only [CollatzResearch.WordTrace]
  refine ⟨67041543499326960175034507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178777449331538560466758685 67041543499326960175034507)
  ·
    refine ⟨100562315248990440262551761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67041543499326960175034507 100562315248990440262551761)
    ·
      refine ⟨75421736436742830196913821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100562315248990440262551761 75421736436742830196913821)
      ·
        refine ⟨28283151163778561323842683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75421736436742830196913821 28283151163778561323842683)
        ·
          refine ⟨42424726745667841985764025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28283151163778561323842683 42424726745667841985764025)
          ·
            refine ⟨31818545059250881489323019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42424726745667841985764025 31818545059250881489323019)
            ·
              refine ⟨47727817588876322233984529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31818545059250881489323019 47727817588876322233984529)
              ·
                refine ⟨35795863191657241675488397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47727817588876322233984529 35795863191657241675488397)
                ·
                  refine ⟨13423448696871465628308149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35795863191657241675488397 13423448696871465628308149)
                  ·
                    refine ⟨1258448315331699902653889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13423448696871465628308149 1258448315331699902653889)
                    ·
                      rfl

theorem cell23_7352458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_7352458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352458 prefixEnd_7352458 := by exact prefixLift 7352458
  have htrace : WordTrace (prefixWord ++ tailWord_7352458) baseStart_7352458 baseEnd_7352458 := by
    simpa [prefixWord, tailWord_7352458, baseEnd_7352458] using wordTrace_append hprefix tailTrace_7352458
  have hstable : (prefixWord ++ tailWord_7352458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352458).length < 2 ^ (prefixWord ++ tailWord_7352458).sum := by decide
  have hdescent : baseEnd_7352458 < baseStart_7352458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352472 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 3, 1, 3]
def baseStart_7352472 : Nat := 118140960795 + 7352472 * 2 ^ 59
def prefixEnd_7352472 : Nat := 4983230072969 + 3 ^ 40 * 7352472 * 2
def baseEnd_7352472 : Nat := 3775352134724262653186603

theorem tailTrace_7352472 : CollatzResearch.WordTrace tailWord_7352472 prefixEnd_7352472 3775352134724262653186603 := by
  unfold tailWord_7352472
  simp only [CollatzResearch.WordTrace]
  refine ⟨134083342309628560545573835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178777789746171414060765113 134083342309628560545573835)
  ·
    refine ⟨201125013464442840818360753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134083342309628560545573835 201125013464442840818360753)
    ·
      refine ⟨150843760098332130613770565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201125013464442840818360753 150843760098332130613770565)
      ·
        refine ⟨28283205018437274490081981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150843760098332130613770565 28283205018437274490081981)
        ·
          refine ⟨10606201881913977933780743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28283205018437274490081981 10606201881913977933780743)
          ·
            refine ⟨15909302822870966900671115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10606201881913977933780743 15909302822870966900671115)
            ·
              refine ⟨23863954234306450351006673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15909302822870966900671115 23863954234306450351006673)
              ·
                refine ⟨17897965675729837763255005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23863954234306450351006673 17897965675729837763255005)
                ·
                  refine ⟨6711737128398689161220627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17897965675729837763255005 6711737128398689161220627)
                  ·
                    refine ⟨10067605692598033741830941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6711737128398689161220627 10067605692598033741830941)
                    ·
                      refine ⟨3775352134724262653186603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10067605692598033741830941 3775352134724262653186603)
                      ·
                        rfl

theorem cell23_7352472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_7352472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352472 prefixEnd_7352472 := by exact prefixLift 7352472
  have htrace : WordTrace (prefixWord ++ tailWord_7352472) baseStart_7352472 baseEnd_7352472 := by
    simpa [prefixWord, tailWord_7352472, baseEnd_7352472] using wordTrace_append hprefix tailTrace_7352472
  have hstable : (prefixWord ++ tailWord_7352472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352472).length < 2 ^ (prefixWord ++ tailWord_7352472).sum := by decide
  have hdescent : baseEnd_7352472 < baseStart_7352472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352482 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_7352482 : Nat := 118140960795 + 7352482 * 2 ^ 59
def prefixEnd_7352482 : Nat := 4983230072969 + 3 ^ 40 * 7352482 * 2
def baseEnd_7352482 : Nat := 3775357269530807614061557

theorem tailTrace_7352482 : CollatzResearch.WordTrace tailWord_7352482 prefixEnd_7352482 3775357269530807614061557 := by
  unfold tailWord_7352482
  simp only [CollatzResearch.WordTrace]
  refine ⟨67041762337305223199752925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178778032899480595199341133 67041762337305223199752925)
  ·
    refine ⟨25140660876489458699907347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67041762337305223199752925 25140660876489458699907347)
    ·
      refine ⟨37710991314734188049861021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25140660876489458699907347 37710991314734188049861021)
      ·
        refine ⟨14141621743025320518697883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37710991314734188049861021 14141621743025320518697883)
        ·
          refine ⟨21212432614537980778046825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14141621743025320518697883 21212432614537980778046825)
          ·
            refine ⟨15909324460903485583535119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21212432614537980778046825 15909324460903485583535119)
            ·
              refine ⟨23863986691355228375302679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15909324460903485583535119 23863986691355228375302679)
              ·
                refine ⟨35795980037032842562954019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23863986691355228375302679 35795980037032842562954019)
                ·
                  refine ⟨53693970055549263844431029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35795980037032842562954019 53693970055549263844431029)
                  ·
                    refine ⟨5033809692707743485415409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53693970055549263844431029 5033809692707743485415409)
                    ·
                      refine ⟨3775357269530807614061557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5033809692707743485415409 3775357269530807614061557)
                      ·
                        rfl

theorem cell23_7352482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_7352482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352482 prefixEnd_7352482 := by exact prefixLift 7352482
  have htrace : WordTrace (prefixWord ++ tailWord_7352482) baseStart_7352482 baseEnd_7352482 := by
    simpa [prefixWord, tailWord_7352482, baseEnd_7352482] using wordTrace_append hprefix tailTrace_7352482
  have hstable : (prefixWord ++ tailWord_7352482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352482).length < 2 ^ (prefixWord ++ tailWord_7352482).sum := by decide
  have hdescent : baseEnd_7352482 < baseStart_7352482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352491 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 4]
def baseStart_7352491 : Nat := 118140960795 + 7352491 * 2 ^ 59
def prefixEnd_7352491 : Nat := 4983230072969 + 3 ^ 40 * 7352491 * 2
def baseEnd_7352491 : Nat := 3775361890856698078849015

theorem tailTrace_7352491 : CollatzResearch.WordTrace tailWord_7352491 prefixEnd_7352491 3775361890856698078849015 := by
  unfold tailWord_7352491
  simp only [CollatzResearch.WordTrace]
  refine ⟨268167377606188287336089327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178778251737458858224059551 268167377606188287336089327)
  ·
    refine ⟨402251066409282431004133991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268167377606188287336089327 402251066409282431004133991)
    ·
      refine ⟨603376599613923646506200987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402251066409282431004133991 603376599613923646506200987)
      ·
        refine ⟨905064899420885469759301481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603376599613923646506200987 905064899420885469759301481)
        ·
          refine ⟨678798674565664102319476111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 905064899420885469759301481 678798674565664102319476111)
          ·
            refine ⟨1018198011848496153479214167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678798674565664102319476111 1018198011848496153479214167)
            ·
              refine ⟨1527297017772744230218821251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018198011848496153479214167 1527297017772744230218821251)
              ·
                refine ⟨2290945526659116345328231877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527297017772744230218821251 2290945526659116345328231877)
                ·
                  refine ⟨429552286248584314749043477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2290945526659116345328231877 429552286248584314749043477)
                  ·
                    refine ⟨20135263417902389753861413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 429552286248584314749043477 20135263417902389753861413)
                    ·
                      refine ⟨3775361890856698078849015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20135263417902389753861413 3775361890856698078849015)
                      ·
                        rfl

theorem cell23_7352491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 4].length) (baseStart_7352491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352491 prefixEnd_7352491 := by exact prefixLift 7352491
  have htrace : WordTrace (prefixWord ++ tailWord_7352491) baseStart_7352491 baseEnd_7352491 := by
    simpa [prefixWord, tailWord_7352491, baseEnd_7352491] using wordTrace_append hprefix tailTrace_7352491
  have hstable : (prefixWord ++ tailWord_7352491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352491).length < 2 ^ (prefixWord ++ tailWord_7352491).sum := by decide
  have hdescent : baseEnd_7352491 < baseStart_7352491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352495 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 7, 2, 2]
def baseStart_7352495 : Nat := 118140960795 + 7352495 * 2 ^ 59
def prefixEnd_7352495 : Nat := 4983230072969 + 3 ^ 40 * 7352495 * 2
def baseEnd_7352495 : Nat := 3775363944779316063198997

theorem tailTrace_7352495 : CollatzResearch.WordTrace tailWord_7352495 prefixEnd_7352495 3775363944779316063198997 := by
  unfold tailWord_7352495
  simp only [CollatzResearch.WordTrace]
  refine ⟨268167523498173796019234939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178778348998782530679489959 268167523498173796019234939)
  ·
    refine ⟨402251285247260694028852409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268167523498173796019234939 402251285247260694028852409)
    ·
      refine ⟨301688463935445520521639307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402251285247260694028852409 301688463935445520521639307)
      ·
        refine ⟨452532695903168280782458961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301688463935445520521639307 452532695903168280782458961)
        ·
          refine ⟨339399521927376210586844221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452532695903168280782458961 339399521927376210586844221)
          ·
            refine ⟨127274820722766078970066583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339399521927376210586844221 127274820722766078970066583)
            ·
              refine ⟨190912231084149118455099875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127274820722766078970066583 190912231084149118455099875)
              ·
                refine ⟨286368346626223677682649813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190912231084149118455099875 286368346626223677682649813)
                ·
                  refine ⟨6711758124052117445687105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 286368346626223677682649813 6711758124052117445687105)
                  ·
                    refine ⟨5033818593039088084265329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6711758124052117445687105 5033818593039088084265329)
                    ·
                      refine ⟨3775363944779316063198997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5033818593039088084265329 3775363944779316063198997)
                      ·
                        rfl

theorem cell23_7352495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 2, 2].length) (baseStart_7352495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352495 prefixEnd_7352495 := by exact prefixLift 7352495
  have htrace : WordTrace (prefixWord ++ tailWord_7352495) baseStart_7352495 baseEnd_7352495 := by
    simpa [prefixWord, tailWord_7352495, baseEnd_7352495] using wordTrace_append hprefix tailTrace_7352495
  have hstable : (prefixWord ++ tailWord_7352495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352495).length < 2 ^ (prefixWord ++ tailWord_7352495).sum := by decide
  have hdescent : baseEnd_7352495 < baseStart_7352495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352498 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_7352498 : Nat := 118140960795 + 7352498 * 2 ^ 59
def prefixEnd_7352498 : Nat := 4983230072969 + 3 ^ 40 * 7352498 * 2
def baseEnd_7352498 : Nat := 3775365485221279551461483

theorem tailTrace_7352498 : CollatzResearch.WordTrace tailWord_7352498 prefixEnd_7352498 3775365485221279551461483 := by
  unfold tailWord_7352498
  simp only [CollatzResearch.WordTrace]
  refine ⟨67041908229290731882898537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178778421944775285021062765 67041908229290731882898537)
  ·
    refine ⟨50281431171968048912173903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67041908229290731882898537 50281431171968048912173903)
    ·
      refine ⟨75422146757952073368260855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50281431171968048912173903 75422146757952073368260855)
      ·
        refine ⟨113133220136928110052391283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75422146757952073368260855 113133220136928110052391283)
        ·
          refine ⟨169699830205392165078586925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113133220136928110052391283 169699830205392165078586925)
          ·
            refine ⟨63637436327022061904470097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169699830205392165078586925 63637436327022061904470097)
            ·
              refine ⟨47728077245266546428352573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63637436327022061904470097 47728077245266546428352573)
              ·
                refine ⟨17898028966974954910632215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47728077245266546428352573 17898028966974954910632215)
                ·
                  refine ⟨26847043450462432365948323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17898028966974954910632215 26847043450462432365948323)
                  ·
                    refine ⟨40270565175693648548922485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26847043450462432365948323 40270565175693648548922485)
                    ·
                      refine ⟨3775365485221279551461483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40270565175693648548922485 3775365485221279551461483)
                      ·
                        rfl

theorem cell23_7352498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_7352498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352498 prefixEnd_7352498 := by exact prefixLift 7352498
  have htrace : WordTrace (prefixWord ++ tailWord_7352498) baseStart_7352498 baseEnd_7352498 := by
    simpa [prefixWord, tailWord_7352498, baseEnd_7352498] using wordTrace_append hprefix tailTrace_7352498
  have hstable : (prefixWord ++ tailWord_7352498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352498).length < 2 ^ (prefixWord ++ tailWord_7352498).sum := by decide
  have hdescent : baseEnd_7352498 < baseStart_7352498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352511 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 7]
def baseStart_7352511 : Nat := 118140960795 + 7352511 * 2 ^ 59
def prefixEnd_7352511 : Nat := 4983230072969 + 3 ^ 40 * 7352511 * 2
def baseEnd_7352511 : Nat := 3775372160469788000598923

theorem tailTrace_7352511 : CollatzResearch.WordTrace tailWord_7352511 prefixEnd_7352511 3775372160469788000598923 := by
  unfold tailWord_7352511
  simp only [CollatzResearch.WordTrace]
  refine ⟨268168107066115830751817387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178778738044077220501211591 268168107066115830751817387)
  ·
    refine ⟨402252160599173746127726081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268168107066115830751817387 402252160599173746127726081)
    ·
      refine ⟨301689120449380309595794561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402252160599173746127726081 301689120449380309595794561)
      ·
        refine ⟨226266840337035232196845921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301689120449380309595794561 226266840337035232196845921)
        ·
          refine ⟨169700130252776424147634441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226266840337035232196845921 169700130252776424147634441)
          ·
            refine ⟨127275097689582318110725831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169700130252776424147634441 127275097689582318110725831)
            ·
              refine ⟨190912646534373477166088747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127275097689582318110725831 190912646534373477166088747)
              ·
                refine ⟨286368969801560215749133121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190912646534373477166088747 286368969801560215749133121)
                ·
                  refine ⟨214776727351170161811849841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286368969801560215749133121 214776727351170161811849841)
                  ·
                    refine ⟨161082545513377621358887381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 214776727351170161811849841 161082545513377621358887381)
                    ·
                      refine ⟨3775372160469788000598923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161082545513377621358887381 3775372160469788000598923)
                      ·
                        rfl

theorem cell23_7352511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_7352511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352511 prefixEnd_7352511 := by exact prefixLift 7352511
  have htrace : WordTrace (prefixWord ++ tailWord_7352511) baseStart_7352511 baseEnd_7352511 := by
    simpa [prefixWord, tailWord_7352511, baseEnd_7352511] using wordTrace_append hprefix tailTrace_7352511
  have hstable : (prefixWord ++ tailWord_7352511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352511).length < 2 ^ (prefixWord ++ tailWord_7352511).sum := by decide
  have hdescent : baseEnd_7352511 < baseStart_7352511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352512 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 3, 2, 2]
def baseStart_7352512 : Nat := 118140960795 + 7352512 * 2 ^ 59
def prefixEnd_7352512 : Nat := 4983230072969 + 3 ^ 40 * 7352512 * 2
def baseEnd_7352512 : Nat := 3775372673950442496686419

theorem tailTrace_7352512 : CollatzResearch.WordTrace tailWord_7352512 prefixEnd_7352512 3775372673950442496686419 := by
  unfold tailWord_7352512
  simp only [CollatzResearch.WordTrace]
  refine ⟨134084071769556103961301895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178778762359408138615069193 134084071769556103961301895)
  ·
    refine ⟨201126107654334155941952843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134084071769556103961301895 201126107654334155941952843)
    ·
      refine ⟨301689161481501233912929265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201126107654334155941952843 301689161481501233912929265)
      ·
        refine ⟨226266871111125925434696949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301689161481501233912929265 226266871111125925434696949)
        ·
          refine ⟨21212519166668055509502839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226266871111125925434696949 21212519166668055509502839)
          ·
            refine ⟨31818778750002083264254259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21212519166668055509502839 31818778750002083264254259)
            ·
              refine ⟨47728168125003124896381389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31818778750002083264254259 47728168125003124896381389)
              ·
                refine ⟨17898063046876171836143021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47728168125003124896381389 17898063046876171836143021)
                ·
                  refine ⟨6711773642578564438553633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17898063046876171836143021 6711773642578564438553633)
                  ·
                    refine ⟨5033830231933923328915225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6711773642578564438553633 5033830231933923328915225)
                    ·
                      refine ⟨3775372673950442496686419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5033830231933923328915225 3775372673950442496686419)
                      ·
                        rfl

theorem cell23_7352512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 3, 2, 2].length) (baseStart_7352512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352512 prefixEnd_7352512 := by exact prefixLift 7352512
  have htrace : WordTrace (prefixWord ++ tailWord_7352512) baseStart_7352512 baseEnd_7352512 := by
    simpa [prefixWord, tailWord_7352512, baseEnd_7352512] using wordTrace_append hprefix tailTrace_7352512
  have hstable : (prefixWord ++ tailWord_7352512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352512).length < 2 ^ (prefixWord ++ tailWord_7352512).sum := by decide
  have hdescent : baseEnd_7352512 < baseStart_7352512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352521 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 6]
def baseStart_7352521 : Nat := 118140960795 + 7352521 * 2 ^ 59
def prefixEnd_7352521 : Nat := 4983230072969 + 3 ^ 40 * 7352521 * 2
def baseEnd_7352521 : Nat := 3775377295276332961473877

theorem tailTrace_7352521 : CollatzResearch.WordTrace tailWord_7352521 prefixEnd_7352521 3775377295276332961473877 := by
  unfold tailWord_7352521
  simp only [CollatzResearch.WordTrace]
  refine ⟨268168471796079602459681417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178778981197386401639787611 268168471796079602459681417)
  ·
    refine ⟨201126353847059701844761063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268168471796079602459681417 201126353847059701844761063)
    ·
      refine ⟨301689530770589552767141595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201126353847059701844761063 301689530770589552767141595)
      ·
        refine ⟨452534296155884329150712393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301689530770589552767141595 452534296155884329150712393)
        ·
          refine ⟨339400722116913246863034295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452534296155884329150712393 339400722116913246863034295)
          ·
            refine ⟨509101083175369870294551443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339400722116913246863034295 509101083175369870294551443)
            ·
              refine ⟨763651624763054805441827165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509101083175369870294551443 763651624763054805441827165)
              ·
                refine ⟨286369359286145552040685187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 763651624763054805441827165 286369359286145552040685187)
                ·
                  refine ⟨429554038929218328061027781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286369359286145552040685187 429554038929218328061027781)
                  ·
                    refine ⟨80541382299228436511442709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 429554038929218328061027781 80541382299228436511442709)
                    ·
                      refine ⟨3775377295276332961473877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80541382299228436511442709 3775377295276332961473877)
                      ·
                        rfl

theorem cell23_7352521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_7352521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352521 prefixEnd_7352521 := by exact prefixLift 7352521
  have htrace : WordTrace (prefixWord ++ tailWord_7352521) baseStart_7352521 baseEnd_7352521 := by
    simpa [prefixWord, tailWord_7352521, baseEnd_7352521] using wordTrace_append hprefix tailTrace_7352521
  have hstable : (prefixWord ++ tailWord_7352521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352521).length < 2 ^ (prefixWord ++ tailWord_7352521).sum := by decide
  have hdescent : baseEnd_7352521 < baseStart_7352521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352522 : List Nat := [3, 1, 2, 1, 3, 1, 5, 1, 2, 4]
def baseStart_7352522 : Nat := 118140960795 + 7352522 * 2 ^ 59
def prefixEnd_7352522 : Nat := 4983230072969 + 3 ^ 40 * 7352522 * 2
def baseEnd_7352522 : Nat := 1258459269585662485853791

theorem tailTrace_7352522 : CollatzResearch.WordTrace tailWord_7352522 prefixEnd_7352522 1258459269585662485853791 := by
  unfold tailWord_7352522
  simp only [CollatzResearch.WordTrace]
  refine ⟨67042127067268994907616955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178779005512717319753645213 67042127067268994907616955)
  ·
    refine ⟨100563190600903492361425433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67042127067268994907616955 100563190600903492361425433)
    ·
      refine ⟨75422392950677619271069075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100563190600903492361425433 75422392950677619271069075)
      ·
        refine ⟨113133589426016428906603613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75422392950677619271069075 113133589426016428906603613)
        ·
          refine ⟨42425096034756160839976355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113133589426016428906603613 42425096034756160839976355)
          ·
            refine ⟨63637644052134241259964533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42425096034756160839976355 63637644052134241259964533)
            ·
              refine ⟨5966029129887585118121675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63637644052134241259964533 5966029129887585118121675)
              ·
                refine ⟨8949043694831377677182513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5966029129887585118121675 8949043694831377677182513)
                ·
                  refine ⟨6711782771123533257886885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8949043694831377677182513 6711782771123533257886885)
                  ·
                    refine ⟨1258459269585662485853791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6711782771123533257886885 1258459269585662485853791)
                    ·
                      rfl

theorem cell23_7352522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_7352522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352522 prefixEnd_7352522 := by exact prefixLift 7352522
  have htrace : WordTrace (prefixWord ++ tailWord_7352522) baseStart_7352522 baseEnd_7352522 := by
    simpa [prefixWord, tailWord_7352522, baseEnd_7352522] using wordTrace_append hprefix tailTrace_7352522
  have hstable : (prefixWord ++ tailWord_7352522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352522).length < 2 ^ (prefixWord ++ tailWord_7352522).sum := by decide
  have hdescent : baseEnd_7352522 < baseStart_7352522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352540 : List Nat := [2, 2, 5, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_7352540 : Nat := 118140960795 + 7352540 * 2 ^ 59
def prefixEnd_7352540 : Nat := 4983230072969 + 3 ^ 40 * 7352540 * 2
def baseEnd_7352540 : Nat := 3775387051408768387136291

theorem tailTrace_7352540 : CollatzResearch.WordTrace tailWord_7352540 prefixEnd_7352540 3775387051408768387136291 := by
  unfold tailWord_7352540
  simp only [CollatzResearch.WordTrace]
  refine ⟨134084582391505384352311537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178779443188673845803082049 134084582391505384352311537)
  ·
    refine ⟨100563436793629038264233653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134084582391505384352311537 100563436793629038264233653)
    ·
      refine ⟨9427822199402722337271905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100563436793629038264233653 9427822199402722337271905)
      ·
        refine ⟨7070866649552041752953929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9427822199402722337271905 7070866649552041752953929)
        ·
          refine ⟨5303149987164031314715447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7070866649552041752953929 5303149987164031314715447)
          ·
            refine ⟨7954724980746046972073171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5303149987164031314715447 7954724980746046972073171)
            ·
              refine ⟨11932087471119070458109757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7954724980746046972073171 11932087471119070458109757)
              ·
                refine ⟨4474532801669651421791159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11932087471119070458109757 4474532801669651421791159)
                ·
                  refine ⟨6711799202504477132686739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4474532801669651421791159 6711799202504477132686739)
                  ·
                    refine ⟨10067698803756715699030109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6711799202504477132686739 10067698803756715699030109)
                    ·
                      refine ⟨3775387051408768387136291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10067698803756715699030109 3775387051408768387136291)
                      ·
                        rfl

theorem cell23_7352540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_7352540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352540 prefixEnd_7352540 := by exact prefixLift 7352540
  have htrace : WordTrace (prefixWord ++ tailWord_7352540) baseStart_7352540 baseEnd_7352540 := by
    simpa [prefixWord, tailWord_7352540, baseEnd_7352540] using wordTrace_append hprefix tailTrace_7352540
  have hstable : (prefixWord ++ tailWord_7352540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352540).length < 2 ^ (prefixWord ++ tailWord_7352540).sum := by decide
  have hdescent : baseEnd_7352540 < baseStart_7352540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352545 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 6, 1, 3]
def baseStart_7352545 : Nat := 118140960795 + 7352545 * 2 ^ 59
def prefixEnd_7352545 : Nat := 4983230072969 + 3 ^ 40 * 7352545 * 2
def baseEnd_7352545 : Nat := 3775389618812040867573767

theorem tailTrace_7352545 : CollatzResearch.WordTrace tailWord_7352545 prefixEnd_7352545 3775389618812040867573767 := by
  unfold tailWord_7352545
  simp only [CollatzResearch.WordTrace]
  refine ⟨268169347147992654558555089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178779564765328436372370059 268169347147992654558555089)
  ·
    refine ⟨201127010360994490918916317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268169347147992654558555089 201127010360994490918916317)
    ·
      refine ⟨75422628885372934094593619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201127010360994490918916317 75422628885372934094593619)
      ·
        refine ⟨113133943328059401141890429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75422628885372934094593619 113133943328059401141890429)
        ·
          refine ⟨42425228748022275428208911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113133943328059401141890429 42425228748022275428208911)
          ·
            refine ⟨63637843122033413142313367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42425228748022275428208911 63637843122033413142313367)
            ·
              refine ⟨95456764683050119713470051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63637843122033413142313367 95456764683050119713470051)
              ·
                refine ⟨143185147024575179570205077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95456764683050119713470051 143185147024575179570205077)
                ·
                  refine ⟨6711803766776961542353363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143185147024575179570205077 6711803766776961542353363)
                  ·
                    refine ⟨10067705650165442313530045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6711803766776961542353363 10067705650165442313530045)
                    ·
                      refine ⟨3775389618812040867573767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10067705650165442313530045 3775389618812040867573767)
                      ·
                        rfl

theorem cell23_7352545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_7352545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352545 prefixEnd_7352545 := by exact prefixLift 7352545
  have htrace : WordTrace (prefixWord ++ tailWord_7352545) baseStart_7352545 baseEnd_7352545 := by
    simpa [prefixWord, tailWord_7352545, baseEnd_7352545] using wordTrace_append hprefix tailTrace_7352545
  have hstable : (prefixWord ++ tailWord_7352545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352545).length < 2 ^ (prefixWord ++ tailWord_7352545).sum := by decide
  have hdescent : baseEnd_7352545 < baseStart_7352545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352558 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_7352558 : Nat := 118140960795 + 7352558 * 2 ^ 59
def prefixEnd_7352558 : Nat := 4983230072969 + 3 ^ 40 * 7352558 * 2
def baseEnd_7352558 : Nat := 3775396294060549316711207

theorem tailTrace_7352558 : CollatzResearch.WordTrace tailWord_7352558 prefixEnd_7352558 3775396294060549316711207 := by
  unfold tailWord_7352558
  simp only [CollatzResearch.WordTrace]
  refine ⟨33521227662118194722347291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178779880864630371852518885 33521227662118194722347291)
  ·
    refine ⟨50281841493177292083520937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33521227662118194722347291 50281841493177292083520937)
    ·
      refine ⟨37711381119882969062640703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50281841493177292083520937 37711381119882969062640703)
      ·
        refine ⟨56567071679824453593961055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37711381119882969062640703 56567071679824453593961055)
        ·
          refine ⟨84850607519736680390941583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56567071679824453593961055 84850607519736680390941583)
          ·
            refine ⟨127275911279605020586412375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84850607519736680390941583 127275911279605020586412375)
            ·
              refine ⟨190913866919407530879618563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127275911279605020586412375 190913866919407530879618563)
              ·
                refine ⟨286370800379111296319427845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190913866919407530879618563 286370800379111296319427845)
                ·
                  refine ⟨53694525071083368059892721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286370800379111296319427845 53694525071083368059892721)
                  ·
                    refine ⟨40270893803312526044919541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53694525071083368059892721 40270893803312526044919541)
                    ·
                      refine ⟨3775396294060549316711207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40270893803312526044919541 3775396294060549316711207)
                      ·
                        rfl

theorem cell23_7352558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_7352558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352558 prefixEnd_7352558 := by exact prefixLift 7352558
  have htrace : WordTrace (prefixWord ++ tailWord_7352558) baseStart_7352558 baseEnd_7352558 := by
    simpa [prefixWord, tailWord_7352558, baseEnd_7352558] using wordTrace_append hprefix tailTrace_7352558
  have hstable : (prefixWord ++ tailWord_7352558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352558).length < 2 ^ (prefixWord ++ tailWord_7352558).sum := by decide
  have hdescent : baseEnd_7352558 < baseStart_7352558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352562 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 4, 1, 3]
def baseStart_7352562 : Nat := 118140960795 + 7352562 * 2 ^ 59
def prefixEnd_7352562 : Nat := 4983230072969 + 3 ^ 40 * 7352562 * 2
def baseEnd_7352562 : Nat := 3775398347983167301061189

theorem tailTrace_7352562 : CollatzResearch.WordTrace tailWord_7352562 prefixEnd_7352562 3775398347983167301061189 := by
  unfold tailWord_7352562
  simp only [CollatzResearch.WordTrace]
  refine ⟨67042491797232766615480985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178779978125954044307949293 67042491797232766615480985)
  ·
    refine ⟨50281868847924574961610739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67042491797232766615480985 50281868847924574961610739)
    ·
      refine ⟨75422803271886862442416109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50281868847924574961610739 75422803271886862442416109)
      ·
        refine ⟨28283551226957573415906041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75422803271886862442416109 28283551226957573415906041)
        ·
          refine ⟨21212663420218180061929531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28283551226957573415906041 21212663420218180061929531)
          ·
            refine ⟨31818995130327270092894297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21212663420218180061929531 31818995130327270092894297)
            ·
              refine ⟨23864246347745452569670723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31818995130327270092894297 23864246347745452569670723)
              ·
                refine ⟨35796369521618178854506085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23864246347745452569670723 35796369521618178854506085)
                ·
                  refine ⟨6711819285303408535219891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35796369521618178854506085 6711819285303408535219891)
                  ·
                    refine ⟨10067728927955112802829837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6711819285303408535219891 10067728927955112802829837)
                    ·
                      refine ⟨3775398347983167301061189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10067728927955112802829837 3775398347983167301061189)
                      ·
                        rfl

theorem cell23_7352562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_7352562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352562 prefixEnd_7352562 := by exact prefixLift 7352562
  have htrace : WordTrace (prefixWord ++ tailWord_7352562) baseStart_7352562 baseEnd_7352562 := by
    simpa [prefixWord, tailWord_7352562, baseEnd_7352562] using wordTrace_append hprefix tailTrace_7352562
  have hstable : (prefixWord ++ tailWord_7352562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352562).length < 2 ^ (prefixWord ++ tailWord_7352562).sum := by decide
  have hdescent : baseEnd_7352562 < baseStart_7352562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352588 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_7352588 : Nat := 118140960795 + 7352588 * 2 ^ 59
def prefixEnd_7352588 : Nat := 4983230072969 + 3 ^ 40 * 7352588 * 2
def baseEnd_7352588 : Nat := 3775411698480184199336069

theorem tailTrace_7352588 : CollatzResearch.WordTrace tailWord_7352588 prefixEnd_7352588 3775411698480184199336069 := by
  unfold tailWord_7352588
  simp only [CollatzResearch.WordTrace]
  refine ⟨134085457743418436451185209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178780610324557915268246945 134085457743418436451185209)
  ·
    refine ⟨100564093307563827338388907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134085457743418436451185209 100564093307563827338388907)
    ·
      refine ⟨150846139961345741007583361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100564093307563827338388907 150846139961345741007583361)
      ·
        refine ⟨113134604971009305755687521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150846139961345741007583361 113134604971009305755687521)
        ·
          refine ⟨84850953728256979316765641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113134604971009305755687521 84850953728256979316765641)
          ·
            refine ⟨63638215296192734487574231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84850953728256979316765641 63638215296192734487574231)
            ·
              refine ⟨95457322944289101731361347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63638215296192734487574231 95457322944289101731361347)
              ·
                refine ⟨143185984416433652597042021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95457322944289101731361347 143185984416433652597042021)
                ·
                  refine ⟨26847372078081309861945379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143185984416433652597042021 26847372078081309861945379)
                  ·
                    refine ⟨40271058117121964792918069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26847372078081309861945379 40271058117121964792918069)
                    ·
                      refine ⟨3775411698480184199336069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40271058117121964792918069 3775411698480184199336069)
                      ·
                        rfl

theorem cell23_7352588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_7352588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352588 prefixEnd_7352588 := by exact prefixLift 7352588
  have htrace : WordTrace (prefixWord ++ tailWord_7352588) baseStart_7352588 baseEnd_7352588 := by
    simpa [prefixWord, tailWord_7352588, baseEnd_7352588] using wordTrace_append hprefix tailTrace_7352588
  have hstable : (prefixWord ++ tailWord_7352588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352588).length < 2 ^ (prefixWord ++ tailWord_7352588).sum := by decide
  have hdescent : baseEnd_7352588 < baseStart_7352588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352648 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_7352648 : Nat := 118140960795 + 7352648 * 2 ^ 59
def prefixEnd_7352648 : Nat := 4983230072969 + 3 ^ 40 * 7352648 * 2
def baseEnd_7352648 : Nat := 3775442507319453964585793

theorem tailTrace_7352648 : CollatzResearch.WordTrace tailWord_7352648 prefixEnd_7352648 3775442507319453964585793 := by
  unfold tailWord_7352648
  simp only [CollatzResearch.WordTrace]
  refine ⟨134086551933309751574777299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178782069244413002099703065 134086551933309751574777299)
  ·
    refine ⟨201129827899964627362165949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134086551933309751574777299 201129827899964627362165949)
    ·
      refine ⟨75423685462486735260812231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201129827899964627362165949 75423685462486735260812231)
      ·
        refine ⟨113135528193730102891218347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75423685462486735260812231 113135528193730102891218347)
        ·
          refine ⟨169703292290595154336827521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113135528193730102891218347 169703292290595154336827521)
          ·
            refine ⟨127277469217946365752620641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169703292290595154336827521 127277469217946365752620641)
            ·
              refine ⟨95458101913459774314465481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127277469217946365752620641 95458101913459774314465481)
              ·
                refine ⟨71593576435094830735849111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95458101913459774314465481 71593576435094830735849111)
                ·
                  refine ⟨107390364652642246103773667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71593576435094830735849111 107390364652642246103773667)
                  ·
                    refine ⟨161085546978963369155660501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107390364652642246103773667 161085546978963369155660501)
                    ·
                      refine ⟨3775442507319453964585793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161085546978963369155660501 3775442507319453964585793)
                      ·
                        rfl

theorem cell23_7352648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_7352648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352648 prefixEnd_7352648 := by exact prefixLift 7352648
  have htrace : WordTrace (prefixWord ++ tailWord_7352648) baseStart_7352648 baseEnd_7352648 := by
    simpa [prefixWord, tailWord_7352648, baseEnd_7352648] using wordTrace_append hprefix tailTrace_7352648
  have hstable : (prefixWord ++ tailWord_7352648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352648).length < 2 ^ (prefixWord ++ tailWord_7352648).sum := by decide
  have hdescent : baseEnd_7352648 < baseStart_7352648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352675 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 4]
def baseStart_7352675 : Nat := 118140960795 + 7352675 * 2 ^ 59
def prefixEnd_7352675 : Nat := 4983230072969 + 3 ^ 40 * 7352675 * 2
def baseEnd_7352675 : Nat := 3775456371297125358948169

theorem tailTrace_7352675 : CollatzResearch.WordTrace tailWord_7352675 prefixEnd_7352675 3775456371297125358948169 := by
  unfold tailWord_7352675
  simp only [CollatzResearch.WordTrace]
  refine ⟨268174088637521686760787479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178782725758347791173858319 268174088637521686760787479)
  ·
    refine ⟨402261132956282530141181219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268174088637521686760787479 402261132956282530141181219)
    ·
      refine ⟨603391699434423795211771829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402261132956282530141181219 603391699434423795211771829)
      ·
        refine ⟨56567971821977230801103609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 603391699434423795211771829 56567971821977230801103609)
        ·
          refine ⟨42425978866482923100827707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56567971821977230801103609 42425978866482923100827707)
          ·
            refine ⟨63638968299724384651241561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42425978866482923100827707 63638968299724384651241561)
            ·
              refine ⟨47729226224793288488431171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63638968299724384651241561 47729226224793288488431171)
              ·
                refine ⟨71593839337189932732646757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47729226224793288488431171 71593839337189932732646757)
                ·
                  refine ⟨13423844875723112387371267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71593839337189932732646757 13423844875723112387371267)
                  ·
                    refine ⟨20135767313584668581056901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13423844875723112387371267 20135767313584668581056901)
                    ·
                      refine ⟨3775456371297125358948169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20135767313584668581056901 3775456371297125358948169)
                      ·
                        rfl

theorem cell23_7352675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_7352675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352675 prefixEnd_7352675 := by exact prefixLift 7352675
  have htrace : WordTrace (prefixWord ++ tailWord_7352675) baseStart_7352675 baseEnd_7352675 := by
    simpa [prefixWord, tailWord_7352675, baseEnd_7352675] using wordTrace_append hprefix tailTrace_7352675
  have hstable : (prefixWord ++ tailWord_7352675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352675).length < 2 ^ (prefixWord ++ tailWord_7352675).sum := by decide
  have hdescent : baseEnd_7352675 < baseStart_7352675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352695 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 3]
def baseStart_7352695 : Nat := 118140960795 + 7352695 * 2 ^ 59
def prefixEnd_7352695 : Nat := 4983230072969 + 3 ^ 40 * 7352695 * 2
def baseEnd_7352695 : Nat := 3775466640910215280698077

theorem tailTrace_7352695 : CollatzResearch.WordTrace tailWord_7352695 prefixEnd_7352695 3775466640910215280698077 := by
  unfold tailWord_7352695
  simp only [CollatzResearch.WordTrace]
  refine ⟨268174818097449230176515539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178783212064966153451010359 268174818097449230176515539)
  ·
    refine ⟨402262227146173845264773309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268174818097449230176515539 402262227146173845264773309)
    ·
      refine ⟨150848335179815191974289991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402262227146173845264773309 150848335179815191974289991)
      ·
        refine ⟨226272502769722787961434987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150848335179815191974289991 226272502769722787961434987)
        ·
          refine ⟨339408754154584181942152481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226272502769722787961434987 339408754154584181942152481)
          ·
            refine ⟨254556565615938136456614361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339408754154584181942152481 254556565615938136456614361)
            ·
              refine ⟨190917424211953602342460771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254556565615938136456614361 190917424211953602342460771)
              ·
                refine ⟨286376136317930403513691157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190917424211953602342460771 286376136317930403513691157)
                ·
                  refine ⟨13423881389902987664704273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 286376136317930403513691157 13423881389902987664704273)
                  ·
                    refine ⟨10067911042427240748528205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13423881389902987664704273 10067911042427240748528205)
                    ·
                      refine ⟨3775466640910215280698077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10067911042427240748528205 3775466640910215280698077)
                      ·
                        rfl

theorem cell23_7352695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_7352695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352695 prefixEnd_7352695 := by exact prefixLift 7352695
  have htrace : WordTrace (prefixWord ++ tailWord_7352695) baseStart_7352695 baseEnd_7352695 := by
    simpa [prefixWord, tailWord_7352695, baseEnd_7352695] using wordTrace_append hprefix tailTrace_7352695
  have hstable : (prefixWord ++ tailWord_7352695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352695).length < 2 ^ (prefixWord ++ tailWord_7352695).sum := by decide
  have hdescent : baseEnd_7352695 < baseStart_7352695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352698 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 12]
def baseStart_7352698 : Nat := 118140960795 + 7352698 * 2 ^ 59
def prefixEnd_7352698 : Nat := 4983230072969 + 3 ^ 40 * 7352698 * 2
def baseEnd_7352698 : Nat := 419496464594686529884507

theorem tailTrace_7352698 : CollatzResearch.WordTrace tailWord_7352698 prefixEnd_7352698 419496464594686529884507 := by
  unfold tailWord_7352698
  simp only [CollatzResearch.WordTrace]
  refine ⟨67043731879109590422218687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178783285010958907792583165 67043731879109590422218687)
  ·
    refine ⟨100565597818664385633328031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67043731879109590422218687 100565597818664385633328031)
    ·
      refine ⟨150848396727996578449992047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100565597818664385633328031 150848396727996578449992047)
      ·
        refine ⟨226272595091994867674988071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150848396727996578449992047 226272595091994867674988071)
        ·
          refine ⟨339408892637992301512482107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226272595091994867674988071 339408892637992301512482107)
          ·
            refine ⟨509113338956988452268723161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339408892637992301512482107 509113338956988452268723161)
            ·
              refine ⟨381835004217741339201542371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509113338956988452268723161 381835004217741339201542371)
              ·
                refine ⟨572752506326612008802313557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381835004217741339201542371 572752506326612008802313557)
                ·
                  refine ⟨419496464594686529884507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 572752506326612008802313557 419496464594686529884507)
                  ·
                    rfl

theorem cell23_7352698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_7352698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352698 prefixEnd_7352698 := by exact prefixLift 7352698
  have htrace : WordTrace (prefixWord ++ tailWord_7352698) baseStart_7352698 baseEnd_7352698 := by
    simpa [prefixWord, tailWord_7352698, baseEnd_7352698] using wordTrace_append hprefix tailTrace_7352698
  have hstable : (prefixWord ++ tailWord_7352698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352698).length < 2 ^ (prefixWord ++ tailWord_7352698).sum := by decide
  have hdescent : baseEnd_7352698 < baseStart_7352698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352712 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_7352712 : Nat := 118140960795 + 7352712 * 2 ^ 59
def prefixEnd_7352712 : Nat := 4983230072969 + 3 ^ 40 * 7352712 * 2
def baseEnd_7352712 : Nat := 3775475370081341714185499

theorem tailTrace_7352712 : CollatzResearch.WordTrace tailWord_7352712 prefixEnd_7352712 3775475370081341714185499 := by
  unfold tailWord_7352712
  simp only [CollatzResearch.WordTrace]
  refine ⟨134087719069193821039942195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178783625425591761386589593 134087719069193821039942195)
  ·
    refine ⟨201131578603790731559913293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134087719069193821039942195 201131578603790731559913293)
    ·
      refine ⟨75424341976421524334967485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201131578603790731559913293 75424341976421524334967485)
      ·
        refine ⟨28284128241158071625612807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75424341976421524334967485 28284128241158071625612807)
        ·
          refine ⟨42426192361737107438419211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28284128241158071625612807 42426192361737107438419211)
          ·
            refine ⟨63639288542605661157628817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42426192361737107438419211 63639288542605661157628817)
            ·
              refine ⟨47729466406954245868221613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63639288542605661157628817 47729466406954245868221613)
              ·
                refine ⟨17898549902607842200583105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47729466406954245868221613 17898549902607842200583105)
                ·
                  refine ⟨13423912426955881650437329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17898549902607842200583105 13423912426955881650437329)
                  ·
                    refine ⟨10067934320216911237827997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13423912426955881650437329 10067934320216911237827997)
                    ·
                      refine ⟨3775475370081341714185499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10067934320216911237827997 3775475370081341714185499)
                      ·
                        rfl

theorem cell23_7352712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_7352712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352712 prefixEnd_7352712 := by exact prefixLift 7352712
  have htrace : WordTrace (prefixWord ++ tailWord_7352712) baseStart_7352712 baseEnd_7352712 := by
    simpa [prefixWord, tailWord_7352712, baseEnd_7352712] using wordTrace_append hprefix tailTrace_7352712
  have hstable : (prefixWord ++ tailWord_7352712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352712).length < 2 ^ (prefixWord ++ tailWord_7352712).sum := by decide
  have hdescent : baseEnd_7352712 < baseStart_7352712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352736 : List Nat := [2, 1, 1, 4, 1, 4, 3, 2, 1, 4]
def baseStart_7352736 : Nat := 118140960795 + 7352736 * 2 ^ 59
def prefixEnd_7352736 : Nat := 4983230072969 + 3 ^ 40 * 7352736 * 2
def baseEnd_7352736 : Nat := 1258495897872349873428463

theorem tailTrace_7352736 : CollatzResearch.WordTrace tailWord_7352736 prefixEnd_7352736 1258495897872349873428463 := by
  unfold tailWord_7352736
  simp only [CollatzResearch.WordTrace]
  refine ⟨134088156745150347089379031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178784208993533796119172041 134088156745150347089379031)
  ·
    refine ⟨201132235117725520634068547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134088156745150347089379031 201132235117725520634068547)
    ·
      refine ⟨301698352676588280951102821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201132235117725520634068547 301698352676588280951102821)
      ·
        refine ⟨56568441126860302678331779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301698352676588280951102821 56568441126860302678331779)
        ·
          refine ⟨84852661690290454017497669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56568441126860302678331779 84852661690290454017497669)
          ·
            refine ⟨15909874066929460128280813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84852661690290454017497669 15909874066929460128280813)
            ·
              refine ⟨5966202775098547548105305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15909874066929460128280813 5966202775098547548105305)
              ·
                refine ⟨4474652081323910661078979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5966202775098547548105305 4474652081323910661078979)
                ·
                  refine ⟨6711978121985865991618469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4474652081323910661078979 6711978121985865991618469)
                  ·
                    refine ⟨1258495897872349873428463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6711978121985865991618469 1258495897872349873428463)
                    ·
                      rfl

theorem cell23_7352736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 1, 4].length) (baseStart_7352736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352736 prefixEnd_7352736 := by exact prefixLift 7352736
  have htrace : WordTrace (prefixWord ++ tailWord_7352736) baseStart_7352736 baseEnd_7352736 := by
    simpa [prefixWord, tailWord_7352736, baseEnd_7352736] using wordTrace_append hprefix tailTrace_7352736
  have hstable : (prefixWord ++ tailWord_7352736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352736).length < 2 ^ (prefixWord ++ tailWord_7352736).sum := by decide
  have hdescent : baseEnd_7352736 < baseStart_7352736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352749 : List Nat := [1, 5, 2, 2, 2, 1, 1, 3, 6]
def baseStart_7352749 : Nat := 118140960795 + 7352749 * 2 ^ 59
def prefixEnd_7352749 : Nat := 4983230072969 + 3 ^ 40 * 7352749 * 2
def baseEnd_7352749 : Nat := 419499374318395341046981

theorem tailTrace_7352749 : CollatzResearch.WordTrace tailWord_7352749 prefixEnd_7352749 419499374318395341046981 := by
  unfold tailWord_7352749
  simp only [CollatzResearch.WordTrace]
  refine ⟨268176787639253597398981301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178784525092835731599320867 268176787639253597398981301)
  ·
    refine ⟨25141573841180024756154497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268176787639253597398981301 25141573841180024756154497)
    ·
      refine ⟨18856180380885018567115873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25141573841180024756154497 18856180380885018567115873)
      ·
        refine ⟨14142135285663763925336905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18856180380885018567115873 14142135285663763925336905)
        ·
          refine ⟨10606601464247822944002679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14142135285663763925336905 10606601464247822944002679)
          ·
            refine ⟨15909902196371734416004019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10606601464247822944002679 15909902196371734416004019)
            ·
              refine ⟨23864853294557601624006029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15909902196371734416004019 23864853294557601624006029)
              ·
                refine ⟨8949319985459100609002261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23864853294557601624006029 8949319985459100609002261)
                ·
                  refine ⟨419499374318395341046981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8949319985459100609002261 419499374318395341046981)
                  ·
                    rfl

theorem cell23_7352749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_7352749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352749 prefixEnd_7352749 := by exact prefixLift 7352749
  have htrace : WordTrace (prefixWord ++ tailWord_7352749) baseStart_7352749 baseEnd_7352749 := by
    simpa [prefixWord, tailWord_7352749, baseEnd_7352749] using wordTrace_append hprefix tailTrace_7352749
  have hstable : (prefixWord ++ tailWord_7352749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352749).length < 2 ^ (prefixWord ++ tailWord_7352749).sum := by decide
  have hdescent : baseEnd_7352749 < baseStart_7352749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352775 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 3, 6]
def baseStart_7352775 : Nat := 118140960795 + 7352775 * 2 ^ 59
def prefixEnd_7352775 : Nat := 4983230072969 + 3 ^ 40 * 7352775 * 2
def baseEnd_7352775 : Nat := 1258502573120858322565903

theorem tailTrace_7352775 : CollatzResearch.WordTrace tailWord_7352775 prefixEnd_7352775 1258502573120858322565903 := by
  unfold tailWord_7352775
  simp only [CollatzResearch.WordTrace]
  refine ⟨268177735937159403839427779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178785157291439602559618519 268177735937159403839427779)
  ·
    refine ⟨402266603905739105759141669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268177735937159403839427779 402266603905739105759141669)
    ·
      refine ⟨75424988232326082329839063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 402266603905739105759141669 75424988232326082329839063)
      ·
        refine ⟨113137482348489123494758595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75424988232326082329839063 113137482348489123494758595)
        ·
          refine ⟨169706223522733685242137893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113137482348489123494758595 169706223522733685242137893)
          ·
            refine ⟨31819916910512565982900855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169706223522733685242137893 31819916910512565982900855)
            ·
              refine ⟨47729875365768848974351283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31819916910512565982900855 47729875365768848974351283)
              ·
                refine ⟨71594813048653273461526925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47729875365768848974351283 71594813048653273461526925)
                ·
                  refine ⟨26848054893244977548072597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71594813048653273461526925 26848054893244977548072597)
                  ·
                    refine ⟨1258502573120858322565903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26848054893244977548072597 1258502573120858322565903)
                    ·
                      rfl

theorem cell23_7352775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_7352775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352775 prefixEnd_7352775 := by exact prefixLift 7352775
  have htrace : WordTrace (prefixWord ++ tailWord_7352775) baseStart_7352775 baseEnd_7352775 := by
    simpa [prefixWord, tailWord_7352775, baseEnd_7352775] using wordTrace_append hprefix tailTrace_7352775
  have hstable : (prefixWord ++ tailWord_7352775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352775).length < 2 ^ (prefixWord ++ tailWord_7352775).sum := by decide
  have hdescent : baseEnd_7352775 < baseStart_7352775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352812 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 4]
def baseStart_7352812 : Nat := 118140960795 + 7352812 * 2 ^ 59
def prefixEnd_7352812 : Nat := 4983230072969 + 3 ^ 40 * 7352812 * 2
def baseEnd_7352812 : Nat := 3775526718146791322935039

theorem tailTrace_7352812 : CollatzResearch.WordTrace tailWord_7352812 prefixEnd_7352812 3775526718146791322935039 := by
  unfold tailWord_7352812
  simp only [CollatzResearch.WordTrace]
  refine ⟨134089542719012679579262345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178786056958683572772349793 134089542719012679579262345)
  ·
    refine ⟨100567157039259509684446759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134089542719012679579262345 100567157039259509684446759)
    ·
      refine ⟨150850735558889264526670139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100567157039259509684446759 150850735558889264526670139)
      ·
        refine ⟨226276103338333896790005209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150850735558889264526670139 226276103338333896790005209)
        ·
          refine ⟨169707077503750422592503907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226276103338333896790005209 169707077503750422592503907)
          ·
            refine ⟨254560616255625633888755861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169707077503750422592503907 254560616255625633888755861)
            ·
              refine ⟨11932528886982451588535431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 254560616255625633888755861 11932528886982451588535431)
              ·
                refine ⟨17898793330473677382803147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11932528886982451588535431 17898793330473677382803147)
                ·
                  refine ⟨26848189995710516074204721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17898793330473677382803147 26848189995710516074204721)
                  ·
                    refine ⟨20136142496782887055653541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26848189995710516074204721 20136142496782887055653541)
                    ·
                      refine ⟨3775526718146791322935039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20136142496782887055653541 3775526718146791322935039)
                      ·
                        rfl

theorem cell23_7352812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_7352812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352812 prefixEnd_7352812 := by exact prefixLift 7352812
  have htrace : WordTrace (prefixWord ++ tailWord_7352812) baseStart_7352812 baseEnd_7352812 := by
    simpa [prefixWord, tailWord_7352812, baseEnd_7352812] using wordTrace_append hprefix tailTrace_7352812
  have hstable : (prefixWord ++ tailWord_7352812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352812).length < 2 ^ (prefixWord ++ tailWord_7352812).sum := by decide
  have hdescent : baseEnd_7352812 < baseStart_7352812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352833 : List Nat := [1, 2, 4, 1, 3, 1, 1, 5, 1, 2, 2]
def baseStart_7352833 : Nat := 118140960795 + 7352833 * 2 ^ 59
def prefixEnd_7352833 : Nat := 4983230072969 + 3 ^ 40 * 7352833 * 2
def baseEnd_7352833 : Nat := 3775537501240535740772443

theorem tailTrace_7352833 : CollatzResearch.WordTrace tailWord_7352833 prefixEnd_7352833 3775537501240535740772443 := by
  unfold tailWord_7352833
  simp only [CollatzResearch.WordTrace]
  refine ⟨268179851370949279745039153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178786567580632853163359435 268179851370949279745039153)
  ·
    refine ⟨201134888528211959808779365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268179851370949279745039153 201134888528211959808779365)
    ·
      refine ⟨37712791599039742464146131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201134888528211959808779365 37712791599039742464146131)
      ·
        refine ⟨56569187398559613696219197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37712791599039742464146131 56569187398559613696219197)
        ·
          refine ⟨21213445274459855136082199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56569187398559613696219197 21213445274459855136082199)
          ·
            refine ⟨31820167911689782704123299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21213445274459855136082199 31820167911689782704123299)
            ·
              refine ⟨47730251867534674056184949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31820167911689782704123299 47730251867534674056184949)
              ·
                refine ⟨4474711112581375692767339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47730251867534674056184949 4474711112581375692767339)
                ·
                  refine ⟨6712066668872063539151009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4474711112581375692767339 6712066668872063539151009)
                  ·
                    refine ⟨5034050001654047654363257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6712066668872063539151009 5034050001654047654363257)
                    ·
                      refine ⟨3775537501240535740772443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034050001654047654363257 3775537501240535740772443)
                      ·
                        rfl

theorem cell23_7352833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_7352833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352833 prefixEnd_7352833 := by exact prefixLift 7352833
  have htrace : WordTrace (prefixWord ++ tailWord_7352833) baseStart_7352833 baseEnd_7352833 := by
    simpa [prefixWord, tailWord_7352833, baseEnd_7352833] using wordTrace_append hprefix tailTrace_7352833
  have hstable : (prefixWord ++ tailWord_7352833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352833).length < 2 ^ (prefixWord ++ tailWord_7352833).sum := by decide
  have hdescent : baseEnd_7352833 < baseStart_7352833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352836 : List Nat := [2, 3, 2, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_7352836 : Nat := 118140960795 + 7352836 * 2 ^ 59
def prefixEnd_7352836 : Nat := 4983230072969 + 3 ^ 40 * 7352836 * 2
def baseEnd_7352836 : Nat := 3775539041682499229034929

theorem tailTrace_7352836 : CollatzResearch.WordTrace tailWord_7352836 prefixEnd_7352836 3775539041682499229034929 := by
  unfold tailWord_7352836
  simp only [CollatzResearch.WordTrace]
  refine ⟨134089980394969205628699181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178786640526625607504932241 134089980394969205628699181)
  ·
    refine ⟨50283742648113452110762193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134089980394969205628699181 50283742648113452110762193)
    ·
      refine ⟨37712806986085089083071645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50283742648113452110762193 37712806986085089083071645)
      ·
        refine ⟨14142302619781908406151867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37712806986085089083071645 14142302619781908406151867)
        ·
          refine ⟨21213453929672862609227801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14142302619781908406151867 21213453929672862609227801)
          ·
            refine ⟨15910090447254646956920851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21213453929672862609227801 15910090447254646956920851)
            ·
              refine ⟨23865135670881970435381277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15910090447254646956920851 23865135670881970435381277)
              ·
                refine ⟨8949425876580738913267979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23865135670881970435381277 8949425876580738913267979)
                ·
                  refine ⟨13424138814871108369901969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8949425876580738913267979 13424138814871108369901969)
                  ·
                    refine ⟨10068104111153331277426477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13424138814871108369901969 10068104111153331277426477)
                    ·
                      refine ⟨3775539041682499229034929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10068104111153331277426477 3775539041682499229034929)
                      ·
                        rfl

theorem cell23_7352836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_7352836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352836 prefixEnd_7352836 := by exact prefixLift 7352836
  have htrace : WordTrace (prefixWord ++ tailWord_7352836) baseStart_7352836 baseEnd_7352836 := by
    simpa [prefixWord, tailWord_7352836, baseEnd_7352836] using wordTrace_append hprefix tailTrace_7352836
  have hstable : (prefixWord ++ tailWord_7352836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352836).length < 2 ^ (prefixWord ++ tailWord_7352836).sum := by decide
  have hdescent : baseEnd_7352836 < baseStart_7352836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352849 : List Nat := [1, 2, 2, 1, 1, 2, 2, 6, 2, 1, 3]
def baseStart_7352849 : Nat := 118140960795 + 7352849 * 2 ^ 59
def prefixEnd_7352849 : Nat := 4983230072969 + 3 ^ 40 * 7352849 * 2
def baseEnd_7352849 : Nat := 3775545716931007678172369

theorem tailTrace_7352849 : CollatzResearch.WordTrace tailWord_7352849 prefixEnd_7352849 3775545716931007678172369 := by
  unfold tailWord_7352849
  simp only [CollatzResearch.WordTrace]
  refine ⟨268180434938891314477621601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178786956625927542985081067 268180434938891314477621601)
  ·
    refine ⟨201135326204168485858216201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268180434938891314477621601 201135326204168485858216201)
    ·
      refine ⟨150851494653126364393662151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201135326204168485858216201 150851494653126364393662151)
      ·
        refine ⟨226277241979689546590493227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150851494653126364393662151 226277241979689546590493227)
        ·
          refine ⟨339415862969534319885739841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226277241979689546590493227 339415862969534319885739841)
          ·
            refine ⟨254561897227150739914304881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339415862969534319885739841 254561897227150739914304881)
            ·
              refine ⟨190921422920363054935728661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254561897227150739914304881 190921422920363054935728661)
              ·
                refine ⟨8949441699392018200112281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 190921422920363054935728661 8949441699392018200112281)
                ·
                  refine ⟨6712081274544013650084211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8949441699392018200112281 6712081274544013650084211)
                  ·
                    refine ⟨10068121911816020475126317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6712081274544013650084211 10068121911816020475126317)
                    ·
                      refine ⟨3775545716931007678172369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10068121911816020475126317 3775545716931007678172369)
                      ·
                        rfl

theorem cell23_7352849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_7352849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352849 prefixEnd_7352849 := by exact prefixLift 7352849
  have htrace : WordTrace (prefixWord ++ tailWord_7352849) baseStart_7352849 baseEnd_7352849 := by
    simpa [prefixWord, tailWord_7352849, baseEnd_7352849] using wordTrace_append hprefix tailTrace_7352849
  have hstable : (prefixWord ++ tailWord_7352849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352849).length < 2 ^ (prefixWord ++ tailWord_7352849).sum := by decide
  have hdescent : baseEnd_7352849 < baseStart_7352849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352875 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 5]
def baseStart_7352875 : Nat := 118140960795 + 7352875 * 2 ^ 59
def prefixEnd_7352875 : Nat := 4983230072969 + 3 ^ 40 * 7352875 * 2
def baseEnd_7352875 : Nat := 3775559067428024576447249

theorem tailTrace_7352875 : CollatzResearch.WordTrace tailWord_7352875 prefixEnd_7352875 3775559067428024576447249 := by
  unfold tailWord_7352875
  simp only [CollatzResearch.WordTrace]
  refine ⟨268181383236797120918068079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178787588824531413945378719 268181383236797120918068079)
  ·
    refine ⟨402272074855195681377102119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268181383236797120918068079 402272074855195681377102119)
    ·
      refine ⟨603408112282793522065653179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402272074855195681377102119 603408112282793522065653179)
      ·
        refine ⟨905112168424190283098479769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603408112282793522065653179 905112168424190283098479769)
        ·
          refine ⟨678834126318142712323859827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 905112168424190283098479769 678834126318142712323859827)
          ·
            refine ⟨1018251189477214068485789741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678834126318142712323859827 1018251189477214068485789741)
            ·
              refine ⟨381844196053955275682171153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1018251189477214068485789741 381844196053955275682171153)
              ·
                refine ⟨286383147040466456761628365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381844196053955275682171153 286383147040466456761628365)
                ·
                  refine ⟨107393680140174921285610637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286383147040466456761628365 107393680140174921285610637)
                  ·
                    refine ⟨40272630052565595482103989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107393680140174921285610637 40272630052565595482103989)
                    ·
                      refine ⟨3775559067428024576447249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40272630052565595482103989 3775559067428024576447249)
                      ·
                        rfl

theorem cell23_7352875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 5].length) (baseStart_7352875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352875 prefixEnd_7352875 := by exact prefixLift 7352875
  have htrace : WordTrace (prefixWord ++ tailWord_7352875) baseStart_7352875 baseEnd_7352875 := by
    simpa [prefixWord, tailWord_7352875, baseEnd_7352875] using wordTrace_append hprefix tailTrace_7352875
  have hstable : (prefixWord ++ tailWord_7352875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352875).length < 2 ^ (prefixWord ++ tailWord_7352875).sum := by decide
  have hdescent : baseEnd_7352875 < baseStart_7352875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352884 : List Nat := [2, 5, 1, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_7352884 : Nat := 118140960795 + 7352884 * 2 ^ 59
def prefixEnd_7352884 : Nat := 4983230072969 + 3 ^ 40 * 7352884 * 2
def baseEnd_7352884 : Nat := 3775563688753915041234709

theorem tailTrace_7352884 : CollatzResearch.WordTrace tailWord_7352884 prefixEnd_7352884 3775563688753915041234709 := by
  unfold tailWord_7352884
  simp only [CollatzResearch.WordTrace]
  refine ⟨134090855746882257727572853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178787807662509676970097137 134090855746882257727572853)
  ·
    refine ⟨12571017726270211661959955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134090855746882257727572853 12571017726270211661959955)
    ·
      refine ⟨18856526589405317492939933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12571017726270211661959955 18856526589405317492939933)
      ·
        refine ⟨7071197471026994059852475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18856526589405317492939933 7071197471026994059852475)
        ·
          refine ⟨10606796206540491089778713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7071197471026994059852475 10606796206540491089778713)
          ·
            refine ⟨7955097154905368317334035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10606796206540491089778713 7955097154905368317334035)
            ·
              refine ⟨11932645732358052476001053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7955097154905368317334035 11932645732358052476001053)
              ·
                refine ⟨4474742149634269678500395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11932645732358052476001053 4474742149634269678500395)
                ·
                  refine ⟨6712113224451404517750593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4474742149634269678500395 6712113224451404517750593)
                  ·
                    refine ⟨5034084918338553388312945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6712113224451404517750593 5034084918338553388312945)
                    ·
                      refine ⟨3775563688753915041234709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034084918338553388312945 3775563688753915041234709)
                      ·
                        rfl

theorem cell23_7352884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_7352884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352884 prefixEnd_7352884 := by exact prefixLift 7352884
  have htrace : WordTrace (prefixWord ++ tailWord_7352884) baseStart_7352884 baseEnd_7352884 := by
    simpa [prefixWord, tailWord_7352884, baseEnd_7352884] using wordTrace_append hprefix tailTrace_7352884
  have hstable : (prefixWord ++ tailWord_7352884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352884).length < 2 ^ (prefixWord ++ tailWord_7352884).sum := by decide
  have hdescent : baseEnd_7352884 < baseStart_7352884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352889 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 3, 4, 2]
def baseStart_7352889 : Nat := 118140960795 + 7352889 * 2 ^ 59
def prefixEnd_7352889 : Nat := 4983230072969 + 3 ^ 40 * 7352889 * 2
def baseEnd_7352889 : Nat := 3775566256157187521672185

theorem tailTrace_7352889 : CollatzResearch.WordTrace tailWord_7352889 prefixEnd_7352889 3775566256157187521672185 := by
  unfold tailWord_7352889
  simp only [CollatzResearch.WordTrace]
  refine ⟨268181893858746401309077721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178787929239164267539385147 268181893858746401309077721)
  ·
    refine ⟨201136420394059800981808291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268181893858746401309077721 201136420394059800981808291)
    ·
      refine ⟨301704630591089701472712437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201136420394059800981808291 301704630591089701472712437)
      ·
        refine ⟨28284809117914659513066791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 301704630591089701472712437 28284809117914659513066791)
        ·
          refine ⟨42427213676871989269600187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28284809117914659513066791 42427213676871989269600187)
          ·
            refine ⟨63640820515307983904400281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42427213676871989269600187 63640820515307983904400281)
            ·
              refine ⟨47730615386480987928300211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63640820515307983904400281 47730615386480987928300211)
              ·
                refine ⟨71595923079721481892450317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47730615386480987928300211 71595923079721481892450317)
                ·
                  refine ⟨26848471154895555709668869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71595923079721481892450317 26848471154895555709668869)
                  ·
                    refine ⟨5034088341542916695562913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26848471154895555709668869 5034088341542916695562913)
                    ·
                      refine ⟨3775566256157187521672185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034088341542916695562913 3775566256157187521672185)
                      ·
                        rfl

theorem cell23_7352889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_7352889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352889 prefixEnd_7352889 := by exact prefixLift 7352889
  have htrace : WordTrace (prefixWord ++ tailWord_7352889) baseStart_7352889 baseEnd_7352889 := by
    simpa [prefixWord, tailWord_7352889, baseEnd_7352889] using wordTrace_append hprefix tailTrace_7352889
  have hstable : (prefixWord ++ tailWord_7352889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352889).length < 2 ^ (prefixWord ++ tailWord_7352889).sum := by decide
  have hdescent : baseEnd_7352889 < baseStart_7352889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352892 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_7352892 : Nat := 118140960795 + 7352892 * 2 ^ 59
def prefixEnd_7352892 : Nat := 4983230072969 + 3 ^ 40 * 7352892 * 2
def baseEnd_7352892 : Nat := 3775567796599151009934671

theorem tailTrace_7352892 : CollatzResearch.WordTrace tailWord_7352892 prefixEnd_7352892 3775567796599151009934671 := by
  unfold tailWord_7352892
  simp only [CollatzResearch.WordTrace]
  refine ⟨134091001638867766410718465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178788002185157021880957953 134091001638867766410718465)
  ·
    refine ⟨100568251229150824808038849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134091001638867766410718465 100568251229150824808038849)
    ·
      refine ⟨75426188421863118606029137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100568251229150824808038849 75426188421863118606029137)
      ·
        refine ⟨56569641316397338954521853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75426188421863118606029137 56569641316397338954521853)
        ·
          refine ⟨21213615493649002107945695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56569641316397338954521853 21213615493649002107945695)
          ·
            refine ⟨31820423240473503161918543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21213615493649002107945695 31820423240473503161918543)
            ·
              refine ⟨47730634860710254742877815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31820423240473503161918543 47730634860710254742877815)
              ·
                refine ⟨71595952291065382114316723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47730634860710254742877815 71595952291065382114316723)
                ·
                  refine ⟨107393928436598073171475085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71595952291065382114316723 107393928436598073171475085)
                  ·
                    refine ⟨40272723163724277439303157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107393928436598073171475085 40272723163724277439303157)
                    ·
                      refine ⟨3775567796599151009934671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40272723163724277439303157 3775567796599151009934671)
                      ·
                        rfl

theorem cell23_7352892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_7352892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352892 prefixEnd_7352892 := by exact prefixLift 7352892
  have htrace : WordTrace (prefixWord ++ tailWord_7352892) baseStart_7352892 baseEnd_7352892 := by
    simpa [prefixWord, tailWord_7352892, baseEnd_7352892] using wordTrace_append hprefix tailTrace_7352892
  have hstable : (prefixWord ++ tailWord_7352892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352892).length < 2 ^ (prefixWord ++ tailWord_7352892).sum := by decide
  have hdescent : baseEnd_7352892 < baseStart_7352892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352906 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 4, 2, 2]
def baseStart_7352906 : Nat := 118140960795 + 7352906 * 2 ^ 59
def prefixEnd_7352906 : Nat := 4983230072969 + 3 ^ 40 * 7352906 * 2
def baseEnd_7352906 : Nat := 3775574985328313955159607

theorem tailTrace_7352906 : CollatzResearch.WordTrace tailWord_7352906 prefixEnd_7352906 3775574985328313955159607 := by
  unfold tailWord_7352906
  simp only [CollatzResearch.WordTrace]
  refine ⟨67045628474921203303111643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178788342599789875474964381 67045628474921203303111643)
  ·
    refine ⟨100568442712381804954667465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67045628474921203303111643 100568442712381804954667465)
    ·
      refine ⟨75426332034286353716000599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100568442712381804954667465 75426332034286353716000599)
      ·
        refine ⟨113139498051429530574000899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75426332034286353716000599 113139498051429530574000899)
        ·
          refine ⟨169709247077144295861001349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113139498051429530574000899 169709247077144295861001349)
          ·
            refine ⟨31820483826964555473937753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169709247077144295861001349 31820483826964555473937753)
            ·
              refine ⟨23865362870223416605453315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31820483826964555473937753 23865362870223416605453315)
              ·
                refine ⟨35798044305335124908179973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23865362870223416605453315 35798044305335124908179973)
                ·
                  refine ⟨6712133307250335920283745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35798044305335124908179973 6712133307250335920283745)
                  ·
                    refine ⟨5034099980437751940212809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6712133307250335920283745 5034099980437751940212809)
                    ·
                      refine ⟨3775574985328313955159607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034099980437751940212809 3775574985328313955159607)
                      ·
                        rfl

theorem cell23_7352906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_7352906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352906 prefixEnd_7352906 := by exact prefixLift 7352906
  have htrace : WordTrace (prefixWord ++ tailWord_7352906) baseStart_7352906 baseEnd_7352906 := by
    simpa [prefixWord, tailWord_7352906, baseEnd_7352906] using wordTrace_append hprefix tailTrace_7352906
  have hstable : (prefixWord ++ tailWord_7352906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352906).length < 2 ^ (prefixWord ++ tailWord_7352906).sum := by decide
  have hdescent : baseEnd_7352906 < baseStart_7352906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352979 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 2, 4, 2]
def baseStart_7352979 : Nat := 118140960795 + 7352979 * 2 ^ 59
def prefixEnd_7352979 : Nat := 4983230072969 + 3 ^ 40 * 7352979 * 2
def baseEnd_7352979 : Nat := 3775612469416092169546771

theorem tailTrace_7352979 : CollatzResearch.WordTrace tailWord_7352979 prefixEnd_7352979 3775612469416092169546771 := by
  unfold tailWord_7352979
  simp only [CollatzResearch.WordTrace]
  refine ⟨268185176428420346679853991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178790117618946897786569327 268185176428420346679853991)
  ·
    refine ⟨402277764642630520019780987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268185176428420346679853991 402277764642630520019780987)
    ·
      refine ⟨603416646963945780029671481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402277764642630520019780987 603416646963945780029671481)
      ·
        refine ⟨452562485222959335022253611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 603416646963945780029671481 452562485222959335022253611)
        ·
          refine ⟨678843727834439002533380417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452562485222959335022253611 678843727834439002533380417)
          ·
            refine ⟨509132795875829251900035313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 678843727834439002533380417 509132795875829251900035313)
            ·
              refine ⟨381849596906871938925026485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509132795875829251900035313 381849596906871938925026485)
              ·
                refine ⟨35798399710019244274221233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 381849596906871938925026485 35798399710019244274221233)
                ·
                  refine ⟨26848799782514433205665925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35798399710019244274221233 26848799782514433205665925)
                  ·
                    refine ⟨5034149959221456226062361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26848799782514433205665925 5034149959221456226062361)
                    ·
                      refine ⟨3775612469416092169546771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034149959221456226062361 3775612469416092169546771)
                      ·
                        rfl

theorem cell23_7352979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 4, 2].length) (baseStart_7352979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352979 prefixEnd_7352979 := by exact prefixLift 7352979
  have htrace : WordTrace (prefixWord ++ tailWord_7352979) baseStart_7352979 baseEnd_7352979 := by
    simpa [prefixWord, tailWord_7352979, baseEnd_7352979] using wordTrace_append hprefix tailTrace_7352979
  have hstable : (prefixWord ++ tailWord_7352979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352979).length < 2 ^ (prefixWord ++ tailWord_7352979).sum := by decide
  have hdescent : baseEnd_7352979 < baseStart_7352979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352989 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_7352989 : Nat := 118140960795 + 7352989 * 2 ^ 59
def prefixEnd_7352989 : Nat := 4983230072969 + 3 ^ 40 * 7352989 * 2
def baseEnd_7352989 : Nat := 1258539201407545710140575

theorem tailTrace_7352989 : CollatzResearch.WordTrace tailWord_7352989 prefixEnd_7352989 1258539201407545710140575 := by
  unfold tailWord_7352989
  simp only [CollatzResearch.WordTrace]
  refine ⟨268185541158384118387718021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178790360772256078925145347 268185541158384118387718021)
  ·
    refine ⟨50284788967197022197697129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268185541158384118387718021 50284788967197022197697129)
    ·
      refine ⟨37713591725397766648272847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50284788967197022197697129 37713591725397766648272847)
      ·
        refine ⟨56570387588096649972409271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37713591725397766648272847 56570387588096649972409271)
        ·
          refine ⟨84855581382144974958613907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56570387588096649972409271 84855581382144974958613907)
          ·
            refine ⟨127283372073217462437920861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84855581382144974958613907 127283372073217462437920861)
            ·
              refine ⟨47731264527456548414220323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127283372073217462437920861 47731264527456548414220323)
              ·
                refine ⟨71596896791184822621330485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47731264527456548414220323 71596896791184822621330485)
                ·
                  refine ⟨6712209074173577120749733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71596896791184822621330485 6712209074173577120749733)
                  ·
                    refine ⟨1258539201407545710140575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6712209074173577120749733 1258539201407545710140575)
                    ·
                      rfl

theorem cell23_7352989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_7352989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352989 prefixEnd_7352989 := by exact prefixLift 7352989
  have htrace : WordTrace (prefixWord ++ tailWord_7352989) baseStart_7352989 baseEnd_7352989 := by
    simpa [prefixWord, tailWord_7352989, baseEnd_7352989] using wordTrace_append hprefix tailTrace_7352989
  have hstable : (prefixWord ++ tailWord_7352989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352989).length < 2 ^ (prefixWord ++ tailWord_7352989).sum := by decide
  have hdescent : baseEnd_7352989 < baseStart_7352989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352993 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 2, 5]
def baseStart_7352993 : Nat := 118140960795 + 7352993 * 2 ^ 59
def prefixEnd_7352993 : Nat := 4983230072969 + 3 ^ 40 * 7352993 * 2
def baseEnd_7352993 : Nat := 1258539886048418371590569

theorem tailTrace_7352993 : CollatzResearch.WordTrace tailWord_7352993 prefixEnd_7352993 1258539886048418371590569 := by
  unfold tailWord_7352993
  simp only [CollatzResearch.WordTrace]
  refine ⟨268185687050369627070863633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178790458033579751380575755 268185687050369627070863633)
  ·
    refine ⟨201139265287777220303147725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268185687050369627070863633 201139265287777220303147725)
    ·
      refine ⟨75427224482916457613680397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201139265287777220303147725 75427224482916457613680397)
      ·
        refine ⟨28285209181093671605130149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75427224482916457613680397 28285209181093671605130149)
        ·
          refine ⟨5303476721455063425961903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28285209181093671605130149 5303476721455063425961903)
          ·
            refine ⟨7955215082182595138942855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5303476721455063425961903 7955215082182595138942855)
            ·
              refine ⟨11932822623273892708414283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7955215082182595138942855 11932822623273892708414283)
              ·
                refine ⟨17899233934910839062621425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11932822623273892708414283 17899233934910839062621425)
                ·
                  refine ⟨13424425451183129296966069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17899233934910839062621425 13424425451183129296966069)
                  ·
                    refine ⟨1258539886048418371590569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13424425451183129296966069 1258539886048418371590569)
                    ·
                      rfl

theorem cell23_7352993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_7352993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7352993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7352993 prefixEnd_7352993 := by exact prefixLift 7352993
  have htrace : WordTrace (prefixWord ++ tailWord_7352993) baseStart_7352993 baseEnd_7352993 := by
    simpa [prefixWord, tailWord_7352993, baseEnd_7352993] using wordTrace_append hprefix tailTrace_7352993
  have hstable : (prefixWord ++ tailWord_7352993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352993).length < 2 ^ (prefixWord ++ tailWord_7352993).sum := by decide
  have hdescent : baseEnd_7352993 < baseStart_7352993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353056 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 2, 3, 2]
def baseStart_7353056 : Nat := 118140960795 + 7353056 * 2 ^ 59
def prefixEnd_7353056 : Nat := 4983230072969 + 3 ^ 40 * 7353056 * 2
def baseEnd_7353056 : Nat := 3775652007426488368283917

theorem tailTrace_7353056 : CollatzResearch.WordTrace tailWord_7353056 prefixEnd_7353056 3775652007426488368283917 := by
  unfold tailWord_7353056
  simp only [CollatzResearch.WordTrace]
  refine ⟨134093992424570694415203511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178791989899427592553604681 134093992424570694415203511)
  ·
    refine ⟨201140988636856041622805267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134093992424570694415203511 201140988636856041622805267)
    ·
      refine ⟨301711482955284062434207901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201140988636856041622805267 301711482955284062434207901)
      ·
        refine ⟨113141806108231523412827963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301711482955284062434207901 113141806108231523412827963)
        ·
          refine ⟨169712709162347285119241945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113141806108231523412827963 169712709162347285119241945)
          ·
            refine ⟨127284531871760463839431459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169712709162347285119241945 127284531871760463839431459)
            ·
              refine ⟨190926797807640695759147189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127284531871760463839431459 190926797807640695759147189)
              ·
                refine ⟨17899387294466315227420049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190926797807640695759147189 17899387294466315227420049)
                ·
                  refine ⟨13424540470849736420565037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17899387294466315227420049 13424540470849736420565037)
                  ·
                    refine ⟨5034202676568651157711889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13424540470849736420565037 5034202676568651157711889)
                    ·
                      refine ⟨3775652007426488368283917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034202676568651157711889 3775652007426488368283917)
                      ·
                        rfl

theorem cell23_7353056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_7353056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353056 prefixEnd_7353056 := by exact prefixLift 7353056
  have htrace : WordTrace (prefixWord ++ tailWord_7353056) baseStart_7353056 baseEnd_7353056 := by
    simpa [prefixWord, tailWord_7353056, baseEnd_7353056] using wordTrace_append hprefix tailTrace_7353056
  have hstable : (prefixWord ++ tailWord_7353056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353056).length < 2 ^ (prefixWord ++ tailWord_7353056).sum := by decide
  have hdescent : baseEnd_7353056 < baseStart_7353056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353080 : List Nat := [2, 1, 2, 1, 1, 2, 7, 2, 1, 1, 3]
def baseStart_7353080 : Nat := 118140960795 + 7353080 * 2 ^ 59
def prefixEnd_7353080 : Nat := 4983230072969 + 3 ^ 40 * 7353080 * 2
def baseEnd_7353080 : Nat := 3775664330962196274383807

theorem tailTrace_7353080 : CollatzResearch.WordTrace tailWord_7353080 prefixEnd_7353080 3775664330962196274383807 := by
  unfold tailWord_7353080
  simp only [CollatzResearch.WordTrace]
  refine ⟨134094430100527220464640347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178792573467369627286187129 134094430100527220464640347)
  ·
    refine ⟨201141645150790830696960521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134094430100527220464640347 201141645150790830696960521)
    ·
      refine ⟨150856233863093123022720391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201141645150790830696960521 150856233863093123022720391)
      ·
        refine ⟨226284350794639684534080587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150856233863093123022720391 226284350794639684534080587)
        ·
          refine ⟨339426526191959526801120881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226284350794639684534080587 339426526191959526801120881)
          ·
            refine ⟨254569894643969645100840661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339426526191959526801120881 254569894643969645100840661)
            ·
              refine ⟨5966481905718038557050953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 254569894643969645100840661 5966481905718038557050953)
              ·
                refine ⟨4474861429288528917788215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5966481905718038557050953 4474861429288528917788215)
                ·
                  refine ⟨6712292143932793376682323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4474861429288528917788215 6712292143932793376682323)
                  ·
                    refine ⟨10068438215899190065023485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6712292143932793376682323 10068438215899190065023485)
                    ·
                      refine ⟨3775664330962196274383807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10068438215899190065023485 3775664330962196274383807)
                      ·
                        rfl

theorem cell23_7353080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 1, 1, 3].length) (baseStart_7353080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353080 prefixEnd_7353080 := by exact prefixLift 7353080
  have htrace : WordTrace (prefixWord ++ tailWord_7353080) baseStart_7353080 baseEnd_7353080 := by
    simpa [prefixWord, tailWord_7353080, baseEnd_7353080] using wordTrace_append hprefix tailTrace_7353080
  have hstable : (prefixWord ++ tailWord_7353080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353080).length < 2 ^ (prefixWord ++ tailWord_7353080).sum := by decide
  have hdescent : baseEnd_7353080 < baseStart_7353080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353089 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_7353089 : Nat := 118140960795 + 7353089 * 2 ^ 59
def prefixEnd_7353089 : Nat := 4983230072969 + 3 ^ 40 * 7353089 * 2
def baseEnd_7353089 : Nat := 3775668952288086739171265

theorem tailTrace_7353089 : CollatzResearch.WordTrace tailWord_7353089 prefixEnd_7353089 3775668952288086739171265 := by
  unfold tailWord_7353089
  simp only [CollatzResearch.WordTrace]
  refine ⟨268189188458021835466358321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178792792305347890310905547 268189188458021835466358321)
  ·
    refine ⟨201141891343516376599768741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268189188458021835466358321 201141891343516376599768741)
    ·
      refine ⟨37714104626909320612456639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201141891343516376599768741 37714104626909320612456639)
      ·
        refine ⟨56571156940363980918684959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37714104626909320612456639 56571156940363980918684959)
        ·
          refine ⟨84856735410545971378027439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56571156940363980918684959 84856735410545971378027439)
          ·
            refine ⟨127285103115818957067041159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84856735410545971378027439 127285103115818957067041159)
            ·
              refine ⟨190927654673728435600561739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127285103115818957067041159 190927654673728435600561739)
              ·
                refine ⟨286391482010592653400842609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190927654673728435600561739 286391482010592653400842609)
                ·
                  refine ⟨214793611507944490050631957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286391482010592653400842609 214793611507944490050631957)
                  ·
                    refine ⟨10068450539434897971123373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 214793611507944490050631957 10068450539434897971123373)
                    ·
                      refine ⟨3775668952288086739171265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10068450539434897971123373 3775668952288086739171265)
                      ·
                        rfl

theorem cell23_7353089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_7353089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353089 prefixEnd_7353089 := by exact prefixLift 7353089
  have htrace : WordTrace (prefixWord ++ tailWord_7353089) baseStart_7353089 baseEnd_7353089 := by
    simpa [prefixWord, tailWord_7353089, baseEnd_7353089] using wordTrace_append hprefix tailTrace_7353089
  have hstable : (prefixWord ++ tailWord_7353089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353089).length < 2 ^ (prefixWord ++ tailWord_7353089).sum := by decide
  have hdescent : baseEnd_7353089 < baseStart_7353089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353099 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 4]
def baseStart_7353099 : Nat := 118140960795 + 7353099 * 2 ^ 59
def prefixEnd_7353099 : Nat := 4983230072969 + 3 ^ 40 * 7353099 * 2
def baseEnd_7353099 : Nat := 3775674087094631700046219

theorem tailTrace_7353099 : CollatzResearch.WordTrace tailWord_7353099 prefixEnd_7353099 3775674087094631700046219 := by
  unfold tailWord_7353099
  simp only [CollatzResearch.WordTrace]
  refine ⟨268189553187985607174222351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178793035458657071449481567 268189553187985607174222351)
  ·
    refine ⟨402284329781978410761333527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268189553187985607174222351 402284329781978410761333527)
    ·
      refine ⟨603426494672967616142000291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402284329781978410761333527 603426494672967616142000291)
      ·
        refine ⟨905139742009451424213000437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603426494672967616142000291 905139742009451424213000437)
        ·
          refine ⟨84856850813386071019968791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 905139742009451424213000437 84856850813386071019968791)
          ·
            refine ⟨127285276220079106529953187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84856850813386071019968791 127285276220079106529953187)
            ·
              refine ⟨190927914330118659794929781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127285276220079106529953187 190927914330118659794929781)
              ·
                refine ⟨17899491968448624355774667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190927914330118659794929781 17899491968448624355774667)
                ·
                  refine ⟨26849237952672936533662001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17899491968448624355774667 26849237952672936533662001)
                  ·
                    refine ⟨20136928464504702400246501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26849237952672936533662001 20136928464504702400246501)
                    ·
                      refine ⟨3775674087094631700046219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20136928464504702400246501 3775674087094631700046219)
                      ·
                        rfl

theorem cell23_7353099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 4].length) (baseStart_7353099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353099 prefixEnd_7353099 := by exact prefixLift 7353099
  have htrace : WordTrace (prefixWord ++ tailWord_7353099) baseStart_7353099 baseEnd_7353099 := by
    simpa [prefixWord, tailWord_7353099, baseEnd_7353099] using wordTrace_append hprefix tailTrace_7353099
  have hstable : (prefixWord ++ tailWord_7353099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353099).length < 2 ^ (prefixWord ++ tailWord_7353099).sum := by decide
  have hdescent : baseEnd_7353099 < baseStart_7353099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353116 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_7353116 : Nat := 118140960795 + 7353116 * 2 ^ 59
def prefixEnd_7353116 : Nat := 4983230072969 + 3 ^ 40 * 7353116 * 2
def baseEnd_7353116 : Nat := 3775682816265758133533641

theorem tailTrace_7353116 : CollatzResearch.WordTrace tailWord_7353116 prefixEnd_7353116 3775682816265758133533641 := by
  unfold tailWord_7353116
  simp only [CollatzResearch.WordTrace]
  refine ⟨134095086614462009538795601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178793448819282679385060801 134095086614462009538795601)
  ·
    refine ⟨100571314960846507154096701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134095086614462009538795601 100571314960846507154096701)
    ·
      refine ⟨37714243110317440182786263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100571314960846507154096701 37714243110317440182786263)
      ·
        refine ⟨56571364665476160274179395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37714243110317440182786263 56571364665476160274179395)
        ·
          refine ⟨84857046998214240411269093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56571364665476160274179395 84857046998214240411269093)
          ·
            refine ⟨15910696312165170077112955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84857046998214240411269093 15910696312165170077112955)
            ·
              refine ⟨23866044468247755115669433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15910696312165170077112955 23866044468247755115669433)
              ·
                refine ⟨17899533351185816336752075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23866044468247755115669433 17899533351185816336752075)
                ·
                  refine ⟨26849300026778724505128113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17899533351185816336752075 26849300026778724505128113)
                  ·
                    refine ⟨20136975020084043378846085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26849300026778724505128113 20136975020084043378846085)
                    ·
                      refine ⟨3775682816265758133533641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20136975020084043378846085 3775682816265758133533641)
                      ·
                        rfl

theorem cell23_7353116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_7353116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353116 prefixEnd_7353116 := by exact prefixLift 7353116
  have htrace : WordTrace (prefixWord ++ tailWord_7353116) baseStart_7353116 baseEnd_7353116 := by
    simpa [prefixWord, tailWord_7353116, baseEnd_7353116] using wordTrace_append hprefix tailTrace_7353116
  have hstable : (prefixWord ++ tailWord_7353116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353116).length < 2 ^ (prefixWord ++ tailWord_7353116).sum := by decide
  have hdescent : baseEnd_7353116 < baseStart_7353116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353136 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 4, 1, 3]
def baseStart_7353136 : Nat := 118140960795 + 7353136 * 2 ^ 59
def prefixEnd_7353136 : Nat := 4983230072969 + 3 ^ 40 * 7353136 * 2
def baseEnd_7353136 : Nat := 3775693085878848055283549

theorem tailTrace_7353136 : CollatzResearch.WordTrace tailWord_7353136 prefixEnd_7353136 3775693085878848055283549 := by
  unfold tailWord_7353136
  simp only [CollatzResearch.WordTrace]
  refine ⟨134095451344425781246659631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178793935125901041662212841 134095451344425781246659631)
  ·
    refine ⟨201143177016638671869989447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134095451344425781246659631 201143177016638671869989447)
    ·
      refine ⟨301714765524958007804984171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201143177016638671869989447 301714765524958007804984171)
      ·
        refine ⟨452572148287437011707476257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301714765524958007804984171 452572148287437011707476257)
        ·
          refine ⟨339429111215577758780607193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452572148287437011707476257 339429111215577758780607193)
          ·
            refine ⟨254571833411683319085455395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339429111215577758780607193 254571833411683319085455395)
            ·
              refine ⟨381857750117524978628183093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254571833411683319085455395 381857750117524978628183093)
              ·
                refine ⟨35799164073517966746392165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 381857750117524978628183093 35799164073517966746392165)
                ·
                  refine ⟨6712343263784618764948531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35799164073517966746392165 6712343263784618764948531)
                  ·
                    refine ⟨10068514895676928147422797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6712343263784618764948531 10068514895676928147422797)
                    ·
                      refine ⟨3775693085878848055283549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10068514895676928147422797 3775693085878848055283549)
                      ·
                        rfl

theorem cell23_7353136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 4, 1, 3].length) (baseStart_7353136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353136 prefixEnd_7353136 := by exact prefixLift 7353136
  have htrace : WordTrace (prefixWord ++ tailWord_7353136) baseStart_7353136 baseEnd_7353136 := by
    simpa [prefixWord, tailWord_7353136, baseEnd_7353136] using wordTrace_append hprefix tailTrace_7353136
  have hstable : (prefixWord ++ tailWord_7353136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353136).length < 2 ^ (prefixWord ++ tailWord_7353136).sum := by decide
  have hdescent : baseEnd_7353136 < baseStart_7353136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353139 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 2, 7]
def baseStart_7353139 : Nat := 118140960795 + 7353139 * 2 ^ 59
def prefixEnd_7353139 : Nat := 4983230072969 + 3 ^ 40 * 7353139 * 2
def baseEnd_7353139 : Nat := 1258564875440270514515345

theorem tailTrace_7353139 : CollatzResearch.WordTrace tailWord_7353139 prefixEnd_7353139 1258564875440270514515345 := by
  unfold tailWord_7353139
  simp only [CollatzResearch.WordTrace]
  refine ⟨268191012107840694005678471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178794008071893796003785647 268191012107840694005678471)
  ·
    refine ⟨402286518161761041008517707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268191012107840694005678471 402286518161761041008517707)
    ·
      refine ⟨603429777242641561512776561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402286518161761041008517707 603429777242641561512776561)
      ·
        refine ⟨452572332931981171134582421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 603429777242641561512776561 452572332931981171134582421)
        ·
          refine ⟨21214328106186617396933551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 452572332931981171134582421 21214328106186617396933551)
          ·
            refine ⟨31821492159279926095400327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21214328106186617396933551 31821492159279926095400327)
            ·
              refine ⟨47732238238919889143100491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31821492159279926095400327 47732238238919889143100491)
              ·
                refine ⟨71598357358379833714650737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47732238238919889143100491 71598357358379833714650737)
                ·
                  refine ⟨53698768018784875285988053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71598357358379833714650737 53698768018784875285988053)
                  ·
                    refine ⟨1258564875440270514515345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53698768018784875285988053 1258564875440270514515345)
                    ·
                      rfl

theorem cell23_7353139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 7].length) (baseStart_7353139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353139 prefixEnd_7353139 := by exact prefixLift 7353139
  have htrace : WordTrace (prefixWord ++ tailWord_7353139) baseStart_7353139 baseEnd_7353139 := by
    simpa [prefixWord, tailWord_7353139, baseEnd_7353139] using wordTrace_append hprefix tailTrace_7353139
  have hstable : (prefixWord ++ tailWord_7353139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353139).length < 2 ^ (prefixWord ++ tailWord_7353139).sum := by decide
  have hdescent : baseEnd_7353139 < baseStart_7353139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353159 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_7353159 : Nat := 118140960795 + 7353159 * 2 ^ 59
def prefixEnd_7353159 : Nat := 4983230072969 + 3 ^ 40 * 7353159 * 2
def baseEnd_7353159 : Nat := 3775704895933901465295943

theorem tailTrace_7353159 : CollatzResearch.WordTrace tailWord_7353159 prefixEnd_7353159 3775704895933901465295943 := by
  unfold tailWord_7353159
  simp only [CollatzResearch.WordTrace]
  refine ⟨268191741567768237421406531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178794494378512158280937687 268191741567768237421406531)
  ·
    refine ⟨402287612351652356132109797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268191741567768237421406531 402287612351652356132109797)
    ·
      refine ⟨75428927315934816774770587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 402287612351652356132109797 75428927315934816774770587)
      ·
        refine ⟨113143390973902225162155881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75428927315934816774770587 113143390973902225162155881)
        ·
          refine ⟨84857543230426668871616911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113143390973902225162155881 84857543230426668871616911)
          ·
            refine ⟨127286314845640003307425367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84857543230426668871616911 127286314845640003307425367)
            ·
              refine ⟨190929472268460004961138051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127286314845640003307425367 190929472268460004961138051)
              ·
                refine ⟨286394208402690007441707077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190929472268460004961138051 286394208402690007441707077)
                ·
                  refine ⟨53698914075504376395320077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286394208402690007441707077 53698914075504376395320077)
                  ·
                    refine ⟨20137092778314141148245029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53698914075504376395320077 20137092778314141148245029)
                    ·
                      refine ⟨3775704895933901465295943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20137092778314141148245029 3775704895933901465295943)
                      ·
                        rfl

theorem cell23_7353159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_7353159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353159 prefixEnd_7353159 := by exact prefixLift 7353159
  have htrace : WordTrace (prefixWord ++ tailWord_7353159) baseStart_7353159 baseEnd_7353159 := by
    simpa [prefixWord, tailWord_7353159, baseEnd_7353159] using wordTrace_append hprefix tailTrace_7353159
  have hstable : (prefixWord ++ tailWord_7353159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353159).length < 2 ^ (prefixWord ++ tailWord_7353159).sum := by decide
  have hdescent : baseEnd_7353159 < baseStart_7353159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353214 : List Nat := [4, 2, 3, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_7353214 : Nat := 118140960795 + 7353214 * 2 ^ 59
def prefixEnd_7353214 : Nat := 4983230072969 + 3 ^ 40 * 7353214 * 2
def baseEnd_7353214 : Nat := 3775733137369898750108191

theorem tailTrace_7353214 : CollatzResearch.WordTrace tailWord_7353214 prefixEnd_7353214 3775733137369898750108191 := by
  unfold tailWord_7353214
  simp only [CollatzResearch.WordTrace]
  refine ⟨33524218447821122726832337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178795831721712654543105797 33524218447821122726832337)
  ·
    refine ⟨25143163835865842045124253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33524218447821122726832337 25143163835865842045124253)
    ·
      refine ⟨9428686438449690766921595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25143163835865842045124253 9428686438449690766921595)
      ·
        refine ⟨14143029657674536150382393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9428686438449690766921595 14143029657674536150382393)
        ·
          refine ⟨10607272243255902112786795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14143029657674536150382393 10607272243255902112786795)
          ·
            refine ⟨15910908364883853169180193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10607272243255902112786795 15910908364883853169180193)
            ·
              refine ⟨11933181273662889876885145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15910908364883853169180193 11933181273662889876885145)
              ·
                refine ⟨8949885955247167407663859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11933181273662889876885145 8949885955247167407663859)
                ·
                  refine ⟨13424828932870751111495789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8949885955247167407663859 13424828932870751111495789)
                  ·
                    refine ⟨5034310849826531666810921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13424828932870751111495789 5034310849826531666810921)
                    ·
                      refine ⟨3775733137369898750108191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034310849826531666810921 3775733137369898750108191)
                      ·
                        rfl

theorem cell23_7353214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_7353214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353214 prefixEnd_7353214 := by exact prefixLift 7353214
  have htrace : WordTrace (prefixWord ++ tailWord_7353214) baseStart_7353214 baseEnd_7353214 := by
    simpa [prefixWord, tailWord_7353214, baseEnd_7353214] using wordTrace_append hprefix tailTrace_7353214
  have hstable : (prefixWord ++ tailWord_7353214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353214).length < 2 ^ (prefixWord ++ tailWord_7353214).sum := by decide
  have hdescent : baseEnd_7353214 < baseStart_7353214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353317 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 2, 4, 2]
def baseStart_7353317 : Nat := 118140960795 + 7353317 * 2 ^ 59
def prefixEnd_7353317 : Nat := 4983230072969 + 3 ^ 40 * 7353317 * 2
def baseEnd_7353317 : Nat := 3775786025877311847120217

theorem tailTrace_7353317 : CollatzResearch.WordTrace tailWord_7353317 prefixEnd_7353317 3775786025877311847120217 := by
  unfold tailWord_7353317
  simp only [CollatzResearch.WordTrace]
  refine ⟨268197504301195830405658205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178798336200797220270438803 268197504301195830405658205)
  ·
    refine ⟨100574064112948436402121827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268197504301195830405658205 100574064112948436402121827)
    ·
      refine ⟨150861096169422654603182741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100574064112948436402121827 150861096169422654603182741)
      ·
        refine ⟨7071613882941686934524191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150861096169422654603182741 7071613882941686934524191)
        ·
          refine ⟨10607420824412530401786287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7071613882941686934524191 10607420824412530401786287)
          ·
            refine ⟨15911131236618795602679431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10607420824412530401786287 15911131236618795602679431)
            ·
              refine ⟨23866696854928193404019147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15911131236618795602679431 23866696854928193404019147)
              ·
                refine ⟨35800045282392290106028721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23866696854928193404019147 35800045282392290106028721)
                ·
                  refine ⟨26850033961794217579521541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35800045282392290106028721 26850033961794217579521541)
                  ·
                    refine ⟨5034381367836415796160289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26850033961794217579521541 5034381367836415796160289)
                    ·
                      refine ⟨3775786025877311847120217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034381367836415796160289 3775786025877311847120217)
                      ·
                        rfl

theorem cell23_7353317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_7353317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353317 prefixEnd_7353317 := by exact prefixLift 7353317
  have htrace : WordTrace (prefixWord ++ tailWord_7353317) baseStart_7353317 baseEnd_7353317 := by
    simpa [prefixWord, tailWord_7353317, baseEnd_7353317] using wordTrace_append hprefix tailTrace_7353317
  have hstable : (prefixWord ++ tailWord_7353317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353317).length < 2 ^ (prefixWord ++ tailWord_7353317).sum := by decide
  have hdescent : baseEnd_7353317 < baseStart_7353317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353367 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 3, 1, 3]
def baseStart_7353367 : Nat := 118140960795 + 7353367 * 2 ^ 59
def prefixEnd_7353367 : Nat := 4983230072969 + 3 ^ 40 * 7353367 * 2
def baseEnd_7353367 : Nat := 3775811699910036651494987

theorem tailTrace_7353367 : CollatzResearch.WordTrace tailWord_7353367 prefixEnd_7353367 3775811699910036651494987 := by
  unfold tailWord_7353367
  simp only [CollatzResearch.WordTrace]
  refine ⟨268199327951014688944978355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178799551967343125963318903 268199327951014688944978355)
  ·
    refine ⟨402298991926522033417467533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268199327951014688944978355 402298991926522033417467533)
    ·
      refine ⟨150862121972445762531550325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402298991926522033417467533 150862121972445762531550325)
      ·
        refine ⟨14143323934916790237332843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150862121972445762531550325 14143323934916790237332843)
        ·
          refine ⟨21214985902375185355999265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14143323934916790237332843 21214985902375185355999265)
          ·
            refine ⟨15911239426781389016999449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21214985902375185355999265 15911239426781389016999449)
            ·
              refine ⟨11933429570086041762749587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15911239426781389016999449 11933429570086041762749587)
              ·
                refine ⟨17900144355129062644124381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11933429570086041762749587 17900144355129062644124381)
                ·
                  refine ⟨6712554133173398491546643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17900144355129062644124381 6712554133173398491546643)
                  ·
                    refine ⟨10068831199760097737319965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6712554133173398491546643 10068831199760097737319965)
                    ·
                      refine ⟨3775811699910036651494987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10068831199760097737319965 3775811699910036651494987)
                      ·
                        rfl

theorem cell23_7353367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_7353367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353367 prefixEnd_7353367 := by exact prefixLift 7353367
  have htrace : WordTrace (prefixWord ++ tailWord_7353367) baseStart_7353367 baseEnd_7353367 := by
    simpa [prefixWord, tailWord_7353367, baseEnd_7353367] using wordTrace_append hprefix tailTrace_7353367
  have hstable : (prefixWord ++ tailWord_7353367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353367).length < 2 ^ (prefixWord ++ tailWord_7353367).sum := by decide
  have hdescent : baseEnd_7353367 < baseStart_7353367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353390 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_7353390 : Nat := 118140960795 + 7353390 * 2 ^ 59
def prefixEnd_7353390 : Nat := 4983230072969 + 3 ^ 40 * 7353390 * 2
def baseEnd_7353390 : Nat := 3775823509965090061507381

theorem tailTrace_7353390 : CollatzResearch.WordTrace tailWord_7353390 prefixEnd_7353390 3775823509965090061507381 := by
  unfold tailWord_7353390
  simp only [CollatzResearch.WordTrace]
  refine ⟨33525020853741420484133203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178800111219954242582043749 33525020853741420484133203)
  ·
    refine ⟨50287531280612130726199805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33525020853741420484133203 50287531280612130726199805)
    ·
      refine ⟨18857824230229549022324927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50287531280612130726199805 18857824230229549022324927)
      ·
        refine ⟨28286736345344323533487391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18857824230229549022324927 28286736345344323533487391)
        ·
          refine ⟨42430104518016485300231087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28286736345344323533487391 42430104518016485300231087)
          ·
            refine ⟨63645156777024727950346631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42430104518016485300231087 63645156777024727950346631)
            ·
              refine ⟨95467735165537091925519947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63645156777024727950346631 95467735165537091925519947)
              ·
                refine ⟨143201602748305637888279921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95467735165537091925519947 143201602748305637888279921)
                ·
                  refine ⟨107401202061229228416209941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143201602748305637888279921 107401202061229228416209941)
                  ·
                    refine ⟨5034431346620120082009841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107401202061229228416209941 5034431346620120082009841)
                    ·
                      refine ⟨3775823509965090061507381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034431346620120082009841 3775823509965090061507381)
                      ·
                        rfl

theorem cell23_7353390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_7353390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353390 prefixEnd_7353390 := by exact prefixLift 7353390
  have htrace : WordTrace (prefixWord ++ tailWord_7353390) baseStart_7353390 baseEnd_7353390 := by
    simpa [prefixWord, tailWord_7353390, baseEnd_7353390] using wordTrace_append hprefix tailTrace_7353390
  have hstable : (prefixWord ++ tailWord_7353390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353390).length < 2 ^ (prefixWord ++ tailWord_7353390).sum := by decide
  have hdescent : baseEnd_7353390 < baseStart_7353390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353461 : List Nat := [1, 3, 4, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7353461 : Nat := 118140960795 + 7353461 * 2 ^ 59
def prefixEnd_7353461 : Nat := 4983230072969 + 3 ^ 40 * 7353461 * 2
def baseEnd_7353461 : Nat := 3775859967091559283719555

theorem tailTrace_7353461 : CollatzResearch.WordTrace tailWord_7353461 prefixEnd_7353461 3775859967091559283719555 := by
  unfold tailWord_7353461
  simp only [CollatzResearch.WordTrace]
  refine ⟨268202756412674142998900237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178801837608449428665933491 268202756412674142998900237)
  ·
    refine ⟨100576033654752803624587589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268202756412674142998900237 100576033654752803624587589)
    ·
      refine ⟨18858006310266150679610173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100576033654752803624587589 18858006310266150679610173)
      ·
        refine ⟨7071752366349806504853815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18858006310266150679610173 7071752366349806504853815)
        ·
          refine ⟨10607628549524709757280723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7071752366349806504853815 10607628549524709757280723)
          ·
            refine ⟨15911442824287064635921085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10607628549524709757280723 15911442824287064635921085)
            ·
              refine ⟨5966791059107649238470407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15911442824287064635921085 5966791059107649238470407)
              ·
                refine ⟨8950186588661473857705611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5966791059107649238470407 8950186588661473857705611)
                ·
                  refine ⟨13425279882992210786558417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8950186588661473857705611 13425279882992210786558417)
                  ·
                    refine ⟨10068959912244158089918813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13425279882992210786558417 10068959912244158089918813)
                    ·
                      refine ⟨3775859967091559283719555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10068959912244158089918813 3775859967091559283719555)
                      ·
                        rfl

theorem cell23_7353461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7353461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353461 prefixEnd_7353461 := by exact prefixLift 7353461
  have htrace : WordTrace (prefixWord ++ tailWord_7353461) baseStart_7353461 baseEnd_7353461 := by
    simpa [prefixWord, tailWord_7353461, baseEnd_7353461] using wordTrace_append hprefix tailTrace_7353461
  have hstable : (prefixWord ++ tailWord_7353461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353461).length < 2 ^ (prefixWord ++ tailWord_7353461).sum := by decide
  have hdescent : baseEnd_7353461 < baseStart_7353461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353490 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_7353490 : Nat := 118140960795 + 7353490 * 2 ^ 59
def prefixEnd_7353490 : Nat := 4983230072969 + 3 ^ 40 * 7353490 * 2
def baseEnd_7353490 : Nat := 1258624952676846556752307

theorem tailTrace_7353490 : CollatzResearch.WordTrace tailWord_7353490 prefixEnd_7353490 1258624952676846556752307 := by
  unfold tailWord_7353490
  simp only [CollatzResearch.WordTrace]
  refine ⟨67050953532392270237926481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178802542753046053967803949 67050953532392270237926481)
  ·
    refine ⟨50288215149294202678444861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67050953532392270237926481 50288215149294202678444861)
    ·
      refine ⟨18858080680985326004416823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50288215149294202678444861 18858080680985326004416823)
      ·
        refine ⟨28287121021477989006625235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18858080680985326004416823 28287121021477989006625235)
        ·
          refine ⟨42430681532216983509937853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28287121021477989006625235 42430681532216983509937853)
          ·
            refine ⟨15911505574581368816226695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42430681532216983509937853 15911505574581368816226695)
            ·
              refine ⟨23867258361872053224340043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15911505574581368816226695 23867258361872053224340043)
              ·
                refine ⟨35800887542808079836510065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23867258361872053224340043 35800887542808079836510065)
                ·
                  refine ⟨26850665657106059877382549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35800887542808079836510065 26850665657106059877382549)
                  ·
                    refine ⟨1258624952676846556752307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26850665657106059877382549 1258624952676846556752307)
                    ·
                      rfl

theorem cell23_7353490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_7353490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353490 prefixEnd_7353490 := by exact prefixLift 7353490
  have htrace : WordTrace (prefixWord ++ tailWord_7353490) baseStart_7353490 baseEnd_7353490 := by
    simpa [prefixWord, tailWord_7353490, baseEnd_7353490] using wordTrace_append hprefix tailTrace_7353490
  have hstable : (prefixWord ++ tailWord_7353490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353490).length < 2 ^ (prefixWord ++ tailWord_7353490).sum := by decide
  have hdescent : baseEnd_7353490 < baseStart_7353490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353514 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_7353514 : Nat := 118140960795 + 7353514 * 2 ^ 59
def prefixEnd_7353514 : Nat := 4983230072969 + 3 ^ 40 * 7353514 * 2
def baseEnd_7353514 : Nat := 3775887181566247576356811

theorem tailTrace_7353514 : CollatzResearch.WordTrace tailWord_7353514 prefixEnd_7353514 3775887181566247576356811 := by
  unfold tailWord_7353514
  simp only [CollatzResearch.WordTrace]
  refine ⟨67051172370370533262644899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178803126320988088700386397 67051172370370533262644899)
  ·
    refine ⟨100576758555555799893967349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67051172370370533262644899 100576758555555799893967349)
    ·
      refine ⟨9429071114583356240059439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100576758555555799893967349 9429071114583356240059439)
      ·
        refine ⟨14143606671875034360089159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9429071114583356240059439 14143606671875034360089159)
        ·
          refine ⟨21215410007812551540133739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14143606671875034360089159 21215410007812551540133739)
          ·
            refine ⟨31823115011718827310200609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21215410007812551540133739 31823115011718827310200609)
            ·
              refine ⟨23867336258789120482650457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31823115011718827310200609 23867336258789120482650457)
              ·
                refine ⟨17900502194091840361987843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23867336258789120482650457 17900502194091840361987843)
                ·
                  refine ⟨26850753291137760542981765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17900502194091840361987843 26850753291137760542981765)
                  ·
                    refine ⟨5034516242088330101809081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26850753291137760542981765 5034516242088330101809081)
                    ·
                      refine ⟨3775887181566247576356811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034516242088330101809081 3775887181566247576356811)
                      ·
                        rfl

theorem cell23_7353514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_7353514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353514 prefixEnd_7353514 := by exact prefixLift 7353514
  have htrace : WordTrace (prefixWord ++ tailWord_7353514) baseStart_7353514 baseEnd_7353514 := by
    simpa [prefixWord, tailWord_7353514, baseEnd_7353514] using wordTrace_append hprefix tailTrace_7353514
  have hstable : (prefixWord ++ tailWord_7353514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353514).length < 2 ^ (prefixWord ++ tailWord_7353514).sum := by decide
  have hdescent : baseEnd_7353514 < baseStart_7353514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353537 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 7]
def baseStart_7353537 : Nat := 118140960795 + 7353537 * 2 ^ 59
def prefixEnd_7353537 : Nat := 4983230072969 + 3 ^ 40 * 7353537 * 2
def baseEnd_7353537 : Nat := 419544332402366776263245

theorem tailTrace_7353537 : CollatzResearch.WordTrace tailWord_7353537 prefixEnd_7353537 419544332402366776263245 := by
  unfold tailWord_7353537
  simp only [CollatzResearch.WordTrace]
  refine ⟨268205528360398807978666865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178803685573599205319111243 268205528360398807978666865)
  ·
    refine ⟨201154146270299105984000149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268205528360398807978666865 201154146270299105984000149)
    ·
      refine ⟨9429100606420270593000007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 201154146270299105984000149 9429100606420270593000007)
      ·
        refine ⟨14143650909630405889500011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9429100606420270593000007 14143650909630405889500011)
        ·
          refine ⟨21215476364445608834250017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14143650909630405889500011 21215476364445608834250017)
          ·
            refine ⟨15911607273334206625687513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21215476364445608834250017 15911607273334206625687513)
            ·
              refine ⟨11933705455000654969265635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15911607273334206625687513 11933705455000654969265635)
              ·
                refine ⟨17900558182500982453898453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11933705455000654969265635 17900558182500982453898453)
                ·
                  refine ⟨419544332402366776263245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17900558182500982453898453 419544332402366776263245)
                  ·
                    rfl

theorem cell23_7353537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 7].length) (baseStart_7353537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353537 prefixEnd_7353537 := by exact prefixLift 7353537
  have htrace : WordTrace (prefixWord ++ tailWord_7353537) baseStart_7353537 baseEnd_7353537 := by
    simpa [prefixWord, tailWord_7353537, baseEnd_7353537] using wordTrace_append hprefix tailTrace_7353537
  have hstable : (prefixWord ++ tailWord_7353537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353537).length < 2 ^ (prefixWord ++ tailWord_7353537).sum := by decide
  have hdescent : baseEnd_7353537 < baseStart_7353537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353543 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_7353543 : Nat := 118140960795 + 7353543 * 2 ^ 59
def prefixEnd_7353543 : Nat := 4983230072969 + 3 ^ 40 * 7353543 * 2
def baseEnd_7353543 : Nat := 3775902072505227962894177

theorem tailTrace_7353543 : CollatzResearch.WordTrace tailWord_7353543 prefixEnd_7353543 3775902072505227962894177 := by
  unfold tailWord_7353543
  simp only [CollatzResearch.WordTrace]
  refine ⟨268205747198377071003385283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178803831465584714002256855 268205747198377071003385283)
  ·
    refine ⟨402308620797565606505077925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268205747198377071003385283 402308620797565606505077925)
    ·
      refine ⟨75432866399543551219702111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 402308620797565606505077925 75432866399543551219702111)
      ·
        refine ⟨113149299599315326829553167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75432866399543551219702111 113149299599315326829553167)
        ·
          refine ⟨169723949398972990244329751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113149299599315326829553167 169723949398972990244329751)
          ·
            refine ⟨254585924098459485366494627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169723949398972990244329751 254585924098459485366494627)
            ·
              refine ⟨381878886147689228049741941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254585924098459485366494627 381878886147689228049741941)
              ·
                refine ⟨35801145576345865129663307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 381878886147689228049741941 35801145576345865129663307)
                ·
                  refine ⟨53701718364518797694494961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35801145576345865129663307 53701718364518797694494961)
                  ·
                    refine ⟨40276288773389098270871221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53701718364518797694494961 40276288773389098270871221)
                    ·
                      refine ⟨3775902072505227962894177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40276288773389098270871221 3775902072505227962894177)
                      ·
                        rfl

theorem cell23_7353543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_7353543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353543 prefixEnd_7353543 := by exact prefixLift 7353543
  have htrace : WordTrace (prefixWord ++ tailWord_7353543) baseStart_7353543 baseEnd_7353543 := by
    simpa [prefixWord, tailWord_7353543, baseEnd_7353543] using wordTrace_append hprefix tailTrace_7353543
  have hstable : (prefixWord ++ tailWord_7353543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353543).length < 2 ^ (prefixWord ++ tailWord_7353543).sum := by decide
  have hdescent : baseEnd_7353543 < baseStart_7353543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353588 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 7]
def baseStart_7353588 : Nat := 118140960795 + 7353588 * 2 ^ 59
def prefixEnd_7353588 : Nat := 4983230072969 + 3 ^ 40 * 7353588 * 2
def baseEnd_7353588 : Nat := 419547242126075587425719

theorem tailTrace_7353588 : CollatzResearch.WordTrace tailWord_7353588 prefixEnd_7353588 419547242126075587425719 := by
  unfold tailWord_7353588
  simp only [CollatzResearch.WordTrace]
  refine ⟨134103694241607021844386709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178804925655476029125848945 134103694241607021844386709)
  ·
    refine ⟨6286110667575329148955627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134103694241607021844386709 6286110667575329148955627)
    ·
      refine ⟨9429166001362993723433441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6286110667575329148955627 9429166001362993723433441)
      ·
        refine ⟨7071874501022245292575081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9429166001362993723433441 7071874501022245292575081)
        ·
          refine ⟨5303905875766683969431311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7071874501022245292575081 5303905875766683969431311)
          ·
            refine ⟨7955858813650025954146967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5303905875766683969431311 7955858813650025954146967)
            ·
              refine ⟨11933788220475038931220451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7955858813650025954146967 11933788220475038931220451)
              ·
                refine ⟨17900682330712558396830677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11933788220475038931220451 17900682330712558396830677)
                ·
                  refine ⟨419547242126075587425719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17900682330712558396830677 419547242126075587425719)
                  ·
                    rfl

theorem cell23_7353588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_7353588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353588 prefixEnd_7353588 := by exact prefixLift 7353588
  have htrace : WordTrace (prefixWord ++ tailWord_7353588) baseStart_7353588 baseEnd_7353588 := by
    simpa [prefixWord, tailWord_7353588, baseEnd_7353588] using wordTrace_append hprefix tailTrace_7353588
  have hstable : (prefixWord ++ tailWord_7353588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353588).length < 2 ^ (prefixWord ++ tailWord_7353588).sum := by decide
  have hdescent : baseEnd_7353588 < baseStart_7353588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353593 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 8]
def baseStart_7353593 : Nat := 118140960795 + 7353593 * 2 ^ 59
def prefixEnd_7353593 : Nat := 4983230072969 + 3 ^ 40 * 7353593 * 2
def baseEnd_7353593 : Nat := 419547527393105863029883

theorem tailTrace_7353593 : CollatzResearch.WordTrace tailWord_7353593 prefixEnd_7353593 419547527393105863029883 := by
  unfold tailWord_7353593
  simp only [CollatzResearch.WordTrace]
  refine ⟨268207570848195929542705433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178805047232130619695136955 268207570848195929542705433)
  ·
    refine ⟨201155678136146947157029075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268207570848195929542705433 201155678136146947157029075)
    ·
      refine ⟨301733517204220420735543613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201155678136146947157029075 301733517204220420735543613)
      ·
        refine ⟨113150068951582657775828855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301733517204220420735543613 113150068951582657775828855)
        ·
          refine ⟨169725103427373986663743283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113150068951582657775828855 169725103427373986663743283)
          ·
            refine ⟨254587655141060979995614925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169725103427373986663743283 254587655141060979995614925)
            ·
              refine ⟨95470370677897867498355597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254587655141060979995614925 95470370677897867498355597)
              ·
                refine ⟨35801389004211700311883349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95470370677897867498355597 35801389004211700311883349)
                ·
                  refine ⟨419547527393105863029883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35801389004211700311883349 419547527393105863029883)
                  ·
                    rfl

theorem cell23_7353593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 8].length) (baseStart_7353593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353593 prefixEnd_7353593 := by exact prefixLift 7353593
  have htrace : WordTrace (prefixWord ++ tailWord_7353593) baseStart_7353593 baseEnd_7353593 := by
    simpa [prefixWord, tailWord_7353593, baseEnd_7353593] using wordTrace_append hprefix tailTrace_7353593
  have hstable : (prefixWord ++ tailWord_7353593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353593).length < 2 ^ (prefixWord ++ tailWord_7353593).sum := by decide
  have hdescent : baseEnd_7353593 < baseStart_7353593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353700 : List Nat := [2, 3, 1, 1, 3, 3, 10]
def baseStart_7353700 : Nat := 118140960795 + 7353700 * 2 ^ 59
def prefixEnd_7353700 : Nat := 4983230072969 + 3 ^ 40 * 7353700 * 2
def baseEnd_7353700 : Nat := 46617070234172640106555

theorem tailTrace_7353700 : CollatzResearch.WordTrace tailWord_7353700 prefixEnd_7353700 46617070234172640106555 := by
  unfold tailWord_7353700
  simp only [CollatzResearch.WordTrace]
  refine ⟨134105736729404143408425277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178807648972538857877900369 134105736729404143408425277)
  ·
    refine ⟨50289651273526553778159479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134105736729404143408425277 50289651273526553778159479)
    ·
      refine ⟨75434476910289830667239219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50289651273526553778159479 75434476910289830667239219)
      ·
        refine ⟨113151715365434746000858829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75434476910289830667239219 113151715365434746000858829)
        ·
          refine ⟨42431893262038029750322061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113151715365434746000858829 42431893262038029750322061)
          ·
            refine ⟨15911959973264261156370773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42431893262038029750322061 15911959973264261156370773)
            ·
              refine ⟨46617070234172640106555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15911959973264261156370773 46617070234172640106555)
              ·
                rfl

theorem cell23_7353700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 10].length) (baseStart_7353700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353700 prefixEnd_7353700 := by exact prefixLift 7353700
  have htrace : WordTrace (prefixWord ++ tailWord_7353700) baseStart_7353700 baseEnd_7353700 := by
    simpa [prefixWord, tailWord_7353700, baseEnd_7353700] using wordTrace_append hprefix tailTrace_7353700
  have hstable : (prefixWord ++ tailWord_7353700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353700).length < 2 ^ (prefixWord ++ tailWord_7353700).sum := by decide
  have hdescent : baseEnd_7353700 < baseStart_7353700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353704 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 4, 4]
def baseStart_7353704 : Nat := 118140960795 + 7353704 * 2 ^ 59
def prefixEnd_7353704 : Nat := 4983230072969 + 3 ^ 40 * 7353704 * 2
def baseEnd_7353704 : Nat := 1258661580963533944326979

theorem tailTrace_7353704 : CollatzResearch.WordTrace tailWord_7353704 prefixEnd_7353704 1258661580963533944326979 := by
  unfold tailWord_7353704
  simp only [CollatzResearch.WordTrace]
  refine ⟨134105809675396897749998083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178807746233862530333330777 134105809675396897749998083)
  ·
    refine ⟨201158714513095346624997125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134105809675396897749998083 201158714513095346624997125)
    ·
      refine ⟨37717258971205377492186961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201158714513095346624997125 37717258971205377492186961)
      ·
        refine ⟨28287944228404033119140221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37717258971205377492186961 28287944228404033119140221)
        ·
          refine ⟨10607979085651512419677583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28287944228404033119140221 10607979085651512419677583)
          ·
            refine ⟨15911968628477268629516375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10607979085651512419677583 15911968628477268629516375)
            ·
              refine ⟨23867952942715902944274563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15911968628477268629516375 23867952942715902944274563)
              ·
                refine ⟨35801929414073854416411845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23867952942715902944274563 35801929414073854416411845)
                ·
                  refine ⟨6712861765138847703077221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35801929414073854416411845 6712861765138847703077221)
                  ·
                    refine ⟨1258661580963533944326979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6712861765138847703077221 1258661580963533944326979)
                    ·
                      rfl

theorem cell23_7353704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_7353704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353704 prefixEnd_7353704 := by exact prefixLift 7353704
  have htrace : WordTrace (prefixWord ++ tailWord_7353704) baseStart_7353704 baseEnd_7353704 := by
    simpa [prefixWord, tailWord_7353704, baseEnd_7353704] using wordTrace_append hprefix tailTrace_7353704
  have hstable : (prefixWord ++ tailWord_7353704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353704).length < 2 ^ (prefixWord ++ tailWord_7353704).sum := by decide
  have hdescent : baseEnd_7353704 < baseStart_7353704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353711 : List Nat := [1, 1, 2, 1, 3, 1, 3, 6, 1, 2, 2]
def baseStart_7353711 : Nat := 118140960795 + 7353711 * 2 ^ 59
def prefixEnd_7353711 : Nat := 4983230072969 + 3 ^ 40 * 7353711 * 2
def baseEnd_7353711 : Nat := 3775988337255183305593405

theorem tailTrace_7353711 : CollatzResearch.WordTrace tailWord_7353711 prefixEnd_7353711 3775988337255183305593405 := by
  unfold tailWord_7353711
  simp only [CollatzResearch.WordTrace]
  refine ⟨268211874661768435695500987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178807916441178957130333991 268211874661768435695500987)
  ·
    refine ⟨402317811992652653543251481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268211874661768435695500987 402317811992652653543251481)
    ·
      refine ⟨301738358994489490157438611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402317811992652653543251481 301738358994489490157438611)
      ·
        refine ⟨452607538491734235236157917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301738358994489490157438611 452607538491734235236157917)
        ·
          refine ⟨169727826934400338213559219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 452607538491734235236157917 169727826934400338213559219)
          ·
            refine ⟨254591740401600507320338829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169727826934400338213559219 254591740401600507320338829)
            ·
              refine ⟨95471902650600190245127061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254591740401600507320338829 95471902650600190245127061)
              ·
                refine ⟨4475245436746883917740331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95471902650600190245127061 4475245436746883917740331)
                ·
                  refine ⟨6712868155120325876610497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4475245436746883917740331 6712868155120325876610497)
                  ·
                    refine ⟨5034651116340244407457873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6712868155120325876610497 5034651116340244407457873)
                    ·
                      refine ⟨3775988337255183305593405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034651116340244407457873 3775988337255183305593405)
                      ·
                        rfl

theorem cell23_7353711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 1, 2, 2].length) (baseStart_7353711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353711 prefixEnd_7353711 := by exact prefixLift 7353711
  have htrace : WordTrace (prefixWord ++ tailWord_7353711) baseStart_7353711 baseEnd_7353711 := by
    simpa [prefixWord, tailWord_7353711, baseEnd_7353711] using wordTrace_append hprefix tailTrace_7353711
  have hstable : (prefixWord ++ tailWord_7353711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353711).length < 2 ^ (prefixWord ++ tailWord_7353711).sum := by decide
  have hdescent : baseEnd_7353711 < baseStart_7353711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353727 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 8, 1, 3]
def baseStart_7353727 : Nat := 118140960795 + 7353727 * 2 ^ 59
def prefixEnd_7353727 : Nat := 4983230072969 + 3 ^ 40 * 7353727 * 2
def baseEnd_7353727 : Nat := 3775996552945655242993331

theorem tailTrace_7353727 : CollatzResearch.WordTrace tailWord_7353727 prefixEnd_7353727 3775996552945655242993331 := by
  unfold tailWord_7353727
  simp only [CollatzResearch.WordTrace]
  refine ⟨268212458229710470428083435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178808305486473646952055623 268212458229710470428083435)
  ·
    refine ⟨402318687344565705642125153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268212458229710470428083435 402318687344565705642125153)
    ·
      refine ⟨301739015508424279231593865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402318687344565705642125153 301739015508424279231593865)
      ·
        refine ⟨226304261631318209423695399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301739015508424279231593865 226304261631318209423695399)
        ·
          refine ⟨339456392446977314135543099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226304261631318209423695399 339456392446977314135543099)
          ·
            refine ⟨509184588670465971203314649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339456392446977314135543099 509184588670465971203314649)
            ·
              refine ⟨381888441502849478402485987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509184588670465971203314649 381888441502849478402485987)
              ·
                refine ⟨572832662254274217603728981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381888441502849478402485987 572832662254274217603728981)
                ·
                  refine ⟨6712882760792275987543699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 572832662254274217603728981 6712882760792275987543699)
                  ·
                    refine ⟨10069324141188413981315549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6712882760792275987543699 10069324141188413981315549)
                    ·
                      refine ⟨3775996552945655242993331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10069324141188413981315549 3775996552945655242993331)
                      ·
                        rfl

theorem cell23_7353727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_7353727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353727 prefixEnd_7353727 := by exact prefixLift 7353727
  have htrace : WordTrace (prefixWord ++ tailWord_7353727) baseStart_7353727 baseEnd_7353727 := by
    simpa [prefixWord, tailWord_7353727, baseEnd_7353727] using wordTrace_append hprefix tailTrace_7353727
  have hstable : (prefixWord ++ tailWord_7353727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353727).length < 2 ^ (prefixWord ++ tailWord_7353727).sum := by decide
  have hdescent : baseEnd_7353727 < baseStart_7353727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353740 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_7353740 : Nat := 118140960795 + 7353740 * 2 ^ 59
def prefixEnd_7353740 : Nat := 4983230072969 + 3 ^ 40 * 7353740 * 2
def baseEnd_7353740 : Nat := 3776003228194163692130771

theorem tailTrace_7353740 : CollatzResearch.WordTrace tailWord_7353740 prefixEnd_7353740 3776003228194163692130771 := by
  unfold tailWord_7353740
  simp only [CollatzResearch.WordTrace]
  refine ⟨134106466189331686824153337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178808621585775582432204449 134106466189331686824153337)
  ·
    refine ⟨100579849641998765118115003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134106466189331686824153337 100579849641998765118115003)
    ·
      refine ⟨150869774462998147677172505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100579849641998765118115003 150869774462998147677172505)
      ·
        refine ⟨113152330847248610757879379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150869774462998147677172505 113152330847248610757879379)
        ·
          refine ⟨169728496270872916136819069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113152330847248610757879379 169728496270872916136819069)
          ·
            refine ⟨63648186101577343551307151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169728496270872916136819069 63648186101577343551307151)
            ·
              refine ⟨95472279152366015326960727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63648186101577343551307151 95472279152366015326960727)
              ·
                refine ⟨143208418728549022990441091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95472279152366015326960727 143208418728549022990441091)
                ·
                  refine ⟨214812628092823534485661637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143208418728549022990441091 214812628092823534485661637)
                  ·
                    refine ⟨40277367767404412716061557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 214812628092823534485661637 40277367767404412716061557)
                    ·
                      refine ⟨3776003228194163692130771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40277367767404412716061557 3776003228194163692130771)
                      ·
                        rfl

theorem cell23_7353740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_7353740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353740 prefixEnd_7353740 := by exact prefixLift 7353740
  have htrace : WordTrace (prefixWord ++ tailWord_7353740) baseStart_7353740 baseEnd_7353740 := by
    simpa [prefixWord, tailWord_7353740, baseEnd_7353740] using wordTrace_append hprefix tailTrace_7353740
  have hstable : (prefixWord ++ tailWord_7353740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353740).length < 2 ^ (prefixWord ++ tailWord_7353740).sum := by decide
  have hdescent : baseEnd_7353740 < baseStart_7353740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353767 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_7353767 : Nat := 118140960795 + 7353767 * 2 ^ 59
def prefixEnd_7353767 : Nat := 4983230072969 + 3 ^ 40 * 7353767 * 2
def baseEnd_7353767 : Nat := 3776017092171835086493147

theorem tailTrace_7353767 : CollatzResearch.WordTrace tailWord_7353767 prefixEnd_7353767 3776017092171835086493147 := by
  unfold tailWord_7353767
  simp only [CollatzResearch.WordTrace]
  refine ⟨268213917149565557259539555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178809278099710371506359703 268213917149565557259539555)
  ·
    refine ⟨402320875724348335889309333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268213917149565557259539555 402320875724348335889309333)
    ·
      refine ⟨18858791049578828244811375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 402320875724348335889309333 18858791049578828244811375)
      ·
        refine ⟨28288186574368242367217063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18858791049578828244811375 28288186574368242367217063)
        ·
          refine ⟨42432279861552363550825595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28288186574368242367217063 42432279861552363550825595)
          ·
            refine ⟨63648419792328545326238393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42432279861552363550825595 63648419792328545326238393)
            ·
              refine ⟨47736314844246408994678795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63648419792328545326238393 47736314844246408994678795)
              ·
                refine ⟨71604472266369613492018193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47736314844246408994678795 71604472266369613492018193)
                ·
                  refine ⟨53703354199777210119013645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71604472266369613492018193 53703354199777210119013645)
                  ·
                    refine ⟨20138757824916453794630117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53703354199777210119013645 20138757824916453794630117)
                    ·
                      refine ⟨3776017092171835086493147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20138757824916453794630117 3776017092171835086493147)
                      ·
                        rfl

theorem cell23_7353767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_7353767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353767 prefixEnd_7353767 := by exact prefixLift 7353767
  have htrace : WordTrace (prefixWord ++ tailWord_7353767) baseStart_7353767 baseEnd_7353767 := by
    simpa [prefixWord, tailWord_7353767, baseEnd_7353767] using wordTrace_append hprefix tailTrace_7353767
  have hstable : (prefixWord ++ tailWord_7353767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353767).length < 2 ^ (prefixWord ++ tailWord_7353767).sum := by decide
  have hdescent : baseEnd_7353767 < baseStart_7353767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353818 : List Nat := [3, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2]
def baseStart_7353818 : Nat := 118140960795 + 7353818 * 2 ^ 59
def prefixEnd_7353818 : Nat := 4983230072969 + 3 ^ 40 * 7353818 * 2
def baseEnd_7353818 : Nat := 3776043279685214386955413

theorem tailTrace_7353818 : CollatzResearch.WordTrace tailWord_7353818 prefixEnd_7353818 3776043279685214386955413 := by
  unfold tailWord_7353818
  simp only [CollatzResearch.WordTrace]
  refine ⟨67053944318095198242411527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178810518181587195313097405 67053944318095198242411527)
  ·
    refine ⟨100580916477142797363617291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67053944318095198242411527 100580916477142797363617291)
    ·
      refine ⟨150871374715714196045425937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100580916477142797363617291 150871374715714196045425937)
      ·
        refine ⟨113153531036785647034069453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150871374715714196045425937 113153531036785647034069453)
        ·
          refine ⟨42432574138794617637776045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113153531036785647034069453 42432574138794617637776045)
          ·
            refine ⟨15912215302047981614166017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42432574138794617637776045 15912215302047981614166017)
            ·
              refine ⟨11934161476535986210624513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15912215302047981614166017 11934161476535986210624513)
              ·
                refine ⟨8950621107401989657968385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11934161476535986210624513 8950621107401989657968385)
                ·
                  refine ⟨6712965830551492243476289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8950621107401989657968385 6712965830551492243476289)
                  ·
                    refine ⟨5034724372913619182607217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6712965830551492243476289 5034724372913619182607217)
                    ·
                      refine ⟨3776043279685214386955413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034724372913619182607217 3776043279685214386955413)
                      ·
                        rfl

theorem cell23_7353818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_7353818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353818 prefixEnd_7353818 := by exact prefixLift 7353818
  have htrace : WordTrace (prefixWord ++ tailWord_7353818) baseStart_7353818 baseEnd_7353818 := by
    simpa [prefixWord, tailWord_7353818, baseEnd_7353818] using wordTrace_append hprefix tailTrace_7353818
  have hstable : (prefixWord ++ tailWord_7353818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353818).length < 2 ^ (prefixWord ++ tailWord_7353818).sum := by decide
  have hdescent : baseEnd_7353818 < baseStart_7353818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353858 : List Nat := [3, 4, 1, 2, 1, 2, 2, 3, 5]
def baseStart_7353858 : Nat := 118140960795 + 7353858 * 2 ^ 59
def prefixEnd_7353858 : Nat := 4983230072969 + 3 ^ 40 * 7353858 * 2
def baseEnd_7353858 : Nat := 419562646545710470050581

theorem tailTrace_7353858 : CollatzResearch.WordTrace tailWord_7353858 prefixEnd_7353858 419562646545710470050581 := by
  unfold tailWord_7353858
  simp only [CollatzResearch.WordTrace]
  refine ⟨67054309048058969950275557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178811490794823919867401485 67054309048058969950275557)
  ·
    refine ⟨12572682946511056865676667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67054309048058969950275557 12572682946511056865676667)
    ·
      refine ⟨18859024419766585298515001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12572682946511056865676667 18859024419766585298515001)
      ·
        refine ⟨14144268314824938973886251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18859024419766585298515001 14144268314824938973886251)
        ·
          refine ⟨21216402472237408460829377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14144268314824938973886251 21216402472237408460829377)
          ·
            refine ⟨15912301854178056345622033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21216402472237408460829377 15912301854178056345622033)
            ·
              refine ⟨11934226390633542259216525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15912301854178056345622033 11934226390633542259216525)
              ·
                refine ⟨4475334896487578347206197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11934226390633542259216525 4475334896487578347206197)
                ·
                  refine ⟨419562646545710470050581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4475334896487578347206197 419562646545710470050581)
                  ·
                    rfl

theorem cell23_7353858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_7353858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353858 prefixEnd_7353858 := by exact prefixLift 7353858
  have htrace : WordTrace (prefixWord ++ tailWord_7353858) baseStart_7353858 baseEnd_7353858 := by
    simpa [prefixWord, tailWord_7353858, baseEnd_7353858] using wordTrace_append hprefix tailTrace_7353858
  have hstable : (prefixWord ++ tailWord_7353858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353858).length < 2 ^ (prefixWord ++ tailWord_7353858).sum := by decide
  have hdescent : baseEnd_7353858 < baseStart_7353858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353869 : List Nat := [1, 7, 1, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_7353869 : Nat := 118140960795 + 7353869 * 2 ^ 59
def prefixEnd_7353869 : Nat := 4983230072969 + 3 ^ 40 * 7353869 * 2
def baseEnd_7353869 : Nat := 3776069467198593687417679

theorem tailTrace_7353869 : CollatzResearch.WordTrace tailWord_7353869 prefixEnd_7353869 3776069467198593687417679 := by
  unfold tailWord_7353869
  simp only [CollatzResearch.WordTrace]
  refine ⟨268217637395196028679752661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178811758263464019119835107 268217637395196028679752661)
  ·
    refine ⟨6286350876449906922181703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 268217637395196028679752661 6286350876449906922181703)
    ·
      refine ⟨9429526314674860383272555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6286350876449906922181703 9429526314674860383272555)
      ·
        refine ⟨14144289472012290574908833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9429526314674860383272555 14144289472012290574908833)
        ·
          refine ⟨10608217104009217931181625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14144289472012290574908833 10608217104009217931181625)
          ·
            refine ⟨7956162828006913448386219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10608217104009217931181625 7956162828006913448386219)
            ·
              refine ⟨11934244242010370172579329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7956162828006913448386219 11934244242010370172579329)
              ·
                refine ⟨8950683181507777629434497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11934244242010370172579329 8950683181507777629434497)
                ·
                  refine ⟨6713012386130833222075873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8950683181507777629434497 6713012386130833222075873)
                  ·
                    refine ⟨5034759289598124916556905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6713012386130833222075873 5034759289598124916556905)
                    ·
                      refine ⟨3776069467198593687417679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034759289598124916556905 3776069467198593687417679)
                      ·
                        rfl

theorem cell23_7353869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_7353869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353869 prefixEnd_7353869 := by exact prefixLift 7353869
  have htrace : WordTrace (prefixWord ++ tailWord_7353869) baseStart_7353869 baseEnd_7353869 := by
    simpa [prefixWord, tailWord_7353869, baseEnd_7353869] using wordTrace_append hprefix tailTrace_7353869
  have hstable : (prefixWord ++ tailWord_7353869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353869).length < 2 ^ (prefixWord ++ tailWord_7353869).sum := by decide
  have hdescent : baseEnd_7353869 < baseStart_7353869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353886 : List Nat := [4, 3, 3, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_7353886 : Nat := 118140960795 + 7353886 * 2 ^ 59
def prefixEnd_7353886 : Nat := 4983230072969 + 3 ^ 40 * 7353886 * 2
def baseEnd_7353886 : Nat := 3776078196369720120905101

theorem tailTrace_7353886 : CollatzResearch.WordTrace tailWord_7353886 prefixEnd_7353886 3776078196369720120905101 := by
  unfold tailWord_7353886
  simp only [CollatzResearch.WordTrace]
  refine ⟨33527282179516805072890189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178812171624089627055414341 33527282179516805072890189)
  ·
    refine ⟨12572730817318801902333821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33527282179516805072890189 12572730817318801902333821)
    ·
      refine ⟨4714774056494550713375183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12572730817318801902333821 4714774056494550713375183)
      ·
        refine ⟨7072161084741826070062775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4714774056494550713375183 7072161084741826070062775)
        ·
          refine ⟨10608241627112739105094163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7072161084741826070062775 10608241627112739105094163)
          ·
            refine ⟨15912362440669108657641245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10608241627112739105094163 15912362440669108657641245)
            ·
              refine ⟨5967135915250915746615467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15912362440669108657641245 5967135915250915746615467)
              ·
                refine ⟨8950703872876373619923201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5967135915250915746615467 8950703872876373619923201)
                ·
                  refine ⟨6713027904657280214942401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8950703872876373619923201 6713027904657280214942401)
                  ·
                    refine ⟨5034770928492960161206801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6713027904657280214942401 5034770928492960161206801)
                    ·
                      refine ⟨3776078196369720120905101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034770928492960161206801 3776078196369720120905101)
                      ·
                        rfl

theorem cell23_7353886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_7353886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353886 prefixEnd_7353886 := by exact prefixLift 7353886
  have htrace : WordTrace (prefixWord ++ tailWord_7353886) baseStart_7353886 baseEnd_7353886 := by
    simpa [prefixWord, tailWord_7353886, baseEnd_7353886] using wordTrace_append hprefix tailTrace_7353886
  have hstable : (prefixWord ++ tailWord_7353886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353886).length < 2 ^ (prefixWord ++ tailWord_7353886).sum := by decide
  have hdescent : baseEnd_7353886 < baseStart_7353886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353948 : List Nat := [2, 2, 4, 1, 2, 3, 2, 1, 6]
def baseStart_7353948 : Nat := 118140960795 + 7353948 * 2 ^ 59
def prefixEnd_7353948 : Nat := 4983230072969 + 3 ^ 40 * 7353948 * 2
def baseEnd_7353948 : Nat := 419567781352255430925535

theorem tailTrace_7353948 : CollatzResearch.WordTrace tailWord_7353948 prefixEnd_7353948 419567781352255430925535 := by
  unfold tailWord_7353948
  simp only [CollatzResearch.WordTrace]
  refine ⟨134110259380954912585939249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178813679174606550114585665 134110259380954912585939249)
  ·
    refine ⟨100582694535716184439454437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134110259380954912585939249 100582694535716184439454437)
    ·
      refine ⟨18859255225446784582397707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100582694535716184439454437 18859255225446784582397707)
      ·
        refine ⟨28288882838170176873596561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18859255225446784582397707 28288882838170176873596561)
        ·
          refine ⟨21216662128627632655197421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28288882838170176873596561 21216662128627632655197421)
          ·
            refine ⟨7956248298235362245699033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21216662128627632655197421 7956248298235362245699033)
            ·
              refine ⟨5967186223676521684274275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7956248298235362245699033 5967186223676521684274275)
              ·
                refine ⟨8950779335514782526411413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5967186223676521684274275 8950779335514782526411413)
                ·
                  refine ⟨419567781352255430925535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8950779335514782526411413 419567781352255430925535)
                  ·
                    rfl

theorem cell23_7353948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 6].length) (baseStart_7353948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353948 prefixEnd_7353948 := by exact prefixLift 7353948
  have htrace : WordTrace (prefixWord ++ tailWord_7353948) baseStart_7353948 baseEnd_7353948 := by
    simpa [prefixWord, tailWord_7353948, baseEnd_7353948] using wordTrace_append hprefix tailTrace_7353948
  have hstable : (prefixWord ++ tailWord_7353948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353948).length < 2 ^ (prefixWord ++ tailWord_7353948).sum := by decide
  have hdescent : baseEnd_7353948 < baseStart_7353948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353968 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 2, 3, 2]
def baseStart_7353968 : Nat := 118140960795 + 7353968 * 2 ^ 59
def prefixEnd_7353968 : Nat := 4983230072969 + 3 ^ 40 * 7353968 * 2
def baseEnd_7353968 : Nat := 3776120301783388800079723

theorem tailTrace_7353968 : CollatzResearch.WordTrace tailWord_7353968 prefixEnd_7353968 3776120301783388800079723 := by
  unfold tailWord_7353968
  simp only [CollatzResearch.WordTrace]
  refine ⟨134110624110918684293803279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178814165481224912391737705 134110624110918684293803279)
  ·
    refine ⟨201165936166378026440704919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134110624110918684293803279 201165936166378026440704919)
    ·
      refine ⟨301748904249567039661057379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201165936166378026440704919 301748904249567039661057379)
      ·
        refine ⟨452623356374350559491586069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301748904249567039661057379 452623356374350559491586069)
        ·
          refine ⟨21216719830047682476168097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 452623356374350559491586069 21216719830047682476168097)
          ·
            refine ⟨15912539872535761857126073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21216719830047682476168097 15912539872535761857126073)
            ·
              refine ⟨11934404904401821392844555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15912539872535761857126073 11934404904401821392844555)
              ·
                refine ⟨17901607356602732089266833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11934404904401821392844555 17901607356602732089266833)
                ·
                  refine ⟨13426205517452049066950125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17901607356602732089266833 13426205517452049066950125)
                  ·
                    refine ⟨5034827069044518400106297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13426205517452049066950125 5034827069044518400106297)
                    ·
                      refine ⟨3776120301783388800079723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034827069044518400106297 3776120301783388800079723)
                      ·
                        rfl

theorem cell23_7353968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 2, 3, 2].length) (baseStart_7353968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353968 prefixEnd_7353968 := by exact prefixLift 7353968
  have htrace : WordTrace (prefixWord ++ tailWord_7353968) baseStart_7353968 baseEnd_7353968 := by
    simpa [prefixWord, tailWord_7353968, baseEnd_7353968] using wordTrace_append hprefix tailTrace_7353968
  have hstable : (prefixWord ++ tailWord_7353968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353968).length < 2 ^ (prefixWord ++ tailWord_7353968).sum := by decide
  have hdescent : baseEnd_7353968 < baseStart_7353968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353991 : List Nat := [1, 1, 4, 2, 1, 3, 1, 4, 2, 4]
def baseStart_7353991 : Nat := 118140960795 + 7353991 * 2 ^ 59
def prefixEnd_7353991 : Nat := 4983230072969 + 3 ^ 40 * 7353991 * 2
def baseEnd_7353991 : Nat := 1258710703946147403364039

theorem tailTrace_7353991 : CollatzResearch.WordTrace tailWord_7353991 prefixEnd_7353991 1258710703946147403364039 := by
  unfold tailWord_7353991
  simp only [CollatzResearch.WordTrace]
  refine ⟨268222087100754043515693827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178814724733836029010462551 268222087100754043515693827)
  ·
    refine ⟨402333130651131065273540741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268222087100754043515693827 402333130651131065273540741)
    ·
      refine ⟨75437461997087074738788889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 402333130651131065273540741 75437461997087074738788889)
      ·
        refine ⟨56578096497815306054091667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75437461997087074738788889 56578096497815306054091667)
        ·
          refine ⟨84867144746722959081137501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56578096497815306054091667 84867144746722959081137501)
          ·
            refine ⟨31825179280021109655426563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84867144746722959081137501 31825179280021109655426563)
            ·
              refine ⟨47737768920031664483139845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31825179280021109655426563 47737768920031664483139845)
              ·
                refine ⟨8950831672505937090588721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47737768920031664483139845 8950831672505937090588721)
                ·
                  refine ⟨6713123754379452817941541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8950831672505937090588721 6713123754379452817941541)
                  ·
                    refine ⟨1258710703946147403364039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6713123754379452817941541 1258710703946147403364039)
                    ·
                      rfl

theorem cell23_7353991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_7353991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353991 prefixEnd_7353991 := by exact prefixLift 7353991
  have htrace : WordTrace (prefixWord ++ tailWord_7353991) baseStart_7353991 baseEnd_7353991 := by
    simpa [prefixWord, tailWord_7353991, baseEnd_7353991] using wordTrace_append hprefix tailTrace_7353991
  have hstable : (prefixWord ++ tailWord_7353991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353991).length < 2 ^ (prefixWord ++ tailWord_7353991).sum := by decide
  have hdescent : baseEnd_7353991 < baseStart_7353991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7353992 : List Nat := [2, 1, 3, 5, 1, 1, 1, 4, 1, 1, 3]
def baseStart_7353992 : Nat := 118140960795 + 7353992 * 2 ^ 59
def prefixEnd_7353992 : Nat := 4983230072969 + 3 ^ 40 * 7353992 * 2
def baseEnd_7353992 : Nat := 3776132625319096706179613

theorem tailTrace_7353992 : CollatzResearch.WordTrace tailWord_7353992 prefixEnd_7353992 3776132625319096706179613 := by
  unfold tailWord_7353992
  simp only [CollatzResearch.WordTrace]
  refine ⟨134111061786875210343240115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178814749049166947124320153 134111061786875210343240115)
  ·
    refine ⟨201166592680312815514860173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134111061786875210343240115 201166592680312815514860173)
    ·
      refine ⟨75437472255117305818072565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201166592680312815514860173 75437472255117305818072565)
      ·
        refine ⟨7072263023917247420444303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75437472255117305818072565 7072263023917247420444303)
        ·
          refine ⟨10608394535875871130666455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7072263023917247420444303 10608394535875871130666455)
          ·
            refine ⟨15912591803813806695999683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10608394535875871130666455 15912591803813806695999683)
            ·
              refine ⟨23868887705720710043999525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15912591803813806695999683 23868887705720710043999525)
              ·
                refine ⟨4475416444822633133249911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23868887705720710043999525 4475416444822633133249911)
                ·
                  refine ⟨6713124667233949699874867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4475416444822633133249911 6713124667233949699874867)
                  ·
                    refine ⟨10069687000850924549812301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6713124667233949699874867 10069687000850924549812301)
                    ·
                      refine ⟨3776132625319096706179613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10069687000850924549812301 3776132625319096706179613)
                      ·
                        rfl

theorem cell23_7353992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_7353992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7353992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7353992 prefixEnd_7353992 := by exact prefixLift 7353992
  have htrace : WordTrace (prefixWord ++ tailWord_7353992) baseStart_7353992 baseEnd_7353992 := by
    simpa [prefixWord, tailWord_7353992, baseEnd_7353992] using wordTrace_append hprefix tailTrace_7353992
  have hstable : (prefixWord ++ tailWord_7353992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7353992).length < 2 ^ (prefixWord ++ tailWord_7353992).sum := by decide
  have hdescent : baseEnd_7353992 < baseStart_7353992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7353992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354027 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 11]
def baseStart_7354027 : Nat := 118140960795 + 7354027 * 2 ^ 59
def prefixEnd_7354027 : Nat := 4983230072969 + 3 ^ 40 * 7354027 * 2
def baseEnd_7354027 : Nat := 3776150597142004069241951

theorem tailTrace_7354027 : CollatzResearch.WordTrace tailWord_7354027 prefixEnd_7354027 3776150597142004069241951 := by
  unfold tailWord_7354027
  simp only [CollatzResearch.WordTrace]
  refine ⟨268223400128623621664004335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178815600085749081109336223 268223400128623621664004335)
  ·
    refine ⟨402335100192935432496006503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268223400128623621664004335 402335100192935432496006503)
    ·
      refine ⟨603502650289403148744009755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402335100192935432496006503 603502650289403148744009755)
      ·
        refine ⟨905253975434104723116014633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603502650289403148744009755 905253975434104723116014633)
        ·
          refine ⟨678940481575578542337010975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 905253975434104723116014633 678940481575578542337010975)
          ·
            refine ⟨1018410722363367813505516463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678940481575578542337010975 1018410722363367813505516463)
            ·
              refine ⟨1527616083545051720258274695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018410722363367813505516463 1527616083545051720258274695)
              ·
                refine ⟨2291424125317577580387412043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527616083545051720258274695 2291424125317577580387412043)
                ·
                  refine ⟨3437136187976366370581118065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2291424125317577580387412043 3437136187976366370581118065)
                  ·
                    refine ⟨2577852140982274777935838549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3437136187976366370581118065 2577852140982274777935838549)
                    ·
                      refine ⟨3776150597142004069241951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2577852140982274777935838549 3776150597142004069241951)
                      ·
                        rfl

theorem cell23_7354027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_7354027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354027 prefixEnd_7354027 := by exact prefixLift 7354027
  have htrace : WordTrace (prefixWord ++ tailWord_7354027) baseStart_7354027 baseEnd_7354027 := by
    simpa [prefixWord, tailWord_7354027, baseEnd_7354027] using wordTrace_append hprefix tailTrace_7354027
  have hstable : (prefixWord ++ tailWord_7354027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354027).length < 2 ^ (prefixWord ++ tailWord_7354027).sum := by decide
  have hdescent : baseEnd_7354027 < baseStart_7354027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354031 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 4, 1, 3]
def baseStart_7354031 : Nat := 118140960795 + 7354031 * 2 ^ 59
def prefixEnd_7354031 : Nat := 4983230072969 + 3 ^ 40 * 7354031 * 2
def baseEnd_7354031 : Nat := 3776152651064622053591933

theorem tailTrace_7354031 : CollatzResearch.WordTrace tailWord_7354031 prefixEnd_7354031 3776152651064622053591933 := by
  unfold tailWord_7354031
  simp only [CollatzResearch.WordTrace]
  refine ⟨268223546020609130347149947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178815697347072753564766631 268223546020609130347149947)
  ·
    refine ⟨402335319030913695520724921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268223546020609130347149947 402335319030913695520724921)
    ·
      refine ⟨301751489273185271640543691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402335319030913695520724921 301751489273185271640543691)
      ·
        refine ⟨452627233909777907460815537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301751489273185271640543691 452627233909777907460815537)
        ·
          refine ⟨339470425432333430595611653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452627233909777907460815537 339470425432333430595611653)
          ·
            refine ⟨63650704768562518236677185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339470425432333430595611653 63650704768562518236677185)
            ·
              refine ⟨47738028576421888677507889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63650704768562518236677185 47738028576421888677507889)
              ·
                refine ⟨35803521432316416508130917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47738028576421888677507889 35803521432316416508130917)
                ·
                  refine ⟨6713160268559328095274547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35803521432316416508130917 6713160268559328095274547)
                  ·
                    refine ⟨10069740402838992142911821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6713160268559328095274547 10069740402838992142911821)
                    ·
                      refine ⟨3776152651064622053591933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10069740402838992142911821 3776152651064622053591933)
                      ·
                        rfl

theorem cell23_7354031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 1, 3].length) (baseStart_7354031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354031 prefixEnd_7354031 := by exact prefixLift 7354031
  have htrace : WordTrace (prefixWord ++ tailWord_7354031) baseStart_7354031 baseEnd_7354031 := by
    simpa [prefixWord, tailWord_7354031, baseEnd_7354031] using wordTrace_append hprefix tailTrace_7354031
  have hstable : (prefixWord ++ tailWord_7354031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354031).length < 2 ^ (prefixWord ++ tailWord_7354031).sum := by decide
  have hdescent : baseEnd_7354031 < baseStart_7354031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354065 : List Nat := [1, 2, 2, 1, 2, 5, 3, 1, 2, 1, 3]
def baseStart_7354065 : Nat := 118140960795 + 7354065 * 2 ^ 59
def prefixEnd_7354065 : Nat := 4983230072969 + 3 ^ 40 * 7354065 * 2
def baseEnd_7354065 : Nat := 3776170109406874920566777

theorem tailTrace_7354065 : CollatzResearch.WordTrace tailWord_7354065 prefixEnd_7354065 3776170109406874920566777 := by
  unfold tailWord_7354065
  simp only [CollatzResearch.WordTrace]
  refine ⟨268224786102485954153887649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178816524068323969435925099 268224786102485954153887649)
  ·
    refine ⟨201168589576864465615415737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268224786102485954153887649 201168589576864465615415737)
    ·
      refine ⟨150876442182648349211561803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201168589576864465615415737 150876442182648349211561803)
      ·
        refine ⟨226314663273972523817342705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150876442182648349211561803 226314663273972523817342705)
        ·
          refine ⟨169735997455479392863007029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226314663273972523817342705 169735997455479392863007029)
          ·
            refine ⟨15912749761451193080906909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169735997455479392863007029 15912749761451193080906909)
            ·
              refine ⟨5967281160544197405340091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15912749761451193080906909 5967281160544197405340091)
              ·
                refine ⟨8950921740816296108010137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5967281160544197405340091 8950921740816296108010137)
                ·
                  refine ⟨6713191305612222081007603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8950921740816296108010137 6713191305612222081007603)
                  ·
                    refine ⟨10069786958418333121511405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6713191305612222081007603 10069786958418333121511405)
                    ·
                      refine ⟨3776170109406874920566777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10069786958418333121511405 3776170109406874920566777)
                      ·
                        rfl

theorem cell23_7354065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 2, 1, 3].length) (baseStart_7354065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354065 prefixEnd_7354065 := by exact prefixLift 7354065
  have htrace : WordTrace (prefixWord ++ tailWord_7354065) baseStart_7354065 baseEnd_7354065 := by
    simpa [prefixWord, tailWord_7354065, baseEnd_7354065] using wordTrace_append hprefix tailTrace_7354065
  have hstable : (prefixWord ++ tailWord_7354065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354065).length < 2 ^ (prefixWord ++ tailWord_7354065).sum := by decide
  have hdescent : baseEnd_7354065 < baseStart_7354065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354111 : List Nat := [1, 1, 2, 2, 1, 3, 2, 6, 5]
def baseStart_7354111 : Nat := 118140960795 + 7354111 * 2 ^ 59
def prefixEnd_7354111 : Nat := 4983230072969 + 3 ^ 40 * 7354111 * 2
def baseEnd_7354111 : Nat := 419577081057442415621285

theorem tailTrace_7354111 : CollatzResearch.WordTrace tailWord_7354111 prefixEnd_7354111 419577081057442415621285 := by
  unfold tailWord_7354111
  simp only [CollatzResearch.WordTrace]
  refine ⟨268226463860319304010062187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178817642573546202673374791 268226463860319304010062187)
  ·
    refine ⟨402339695790478956015093281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268226463860319304010062187 402339695790478956015093281)
    ·
      refine ⟨301754771842859217011319961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402339695790478956015093281 301754771842859217011319961)
      ·
        refine ⟨226316078882144412758489971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301754771842859217011319961 226316078882144412758489971)
        ·
          refine ⟨339474118323216619137734957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226316078882144412758489971 339474118323216619137734957)
          ·
            refine ⟨127302794371206232176650609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339474118323216619137734957 127302794371206232176650609)
            ·
              refine ⟨95477095778404674132487957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127302794371206232176650609 95477095778404674132487957)
              ·
                refine ⟨4475488864612719099960373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95477095778404674132487957 4475488864612719099960373)
                ·
                  refine ⟨419577081057442415621285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4475488864612719099960373 419577081057442415621285)
                  ·
                    rfl

theorem cell23_7354111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 5].length) (baseStart_7354111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354111 prefixEnd_7354111 := by exact prefixLift 7354111
  have htrace : WordTrace (prefixWord ++ tailWord_7354111) baseStart_7354111 baseEnd_7354111 := by
    simpa [prefixWord, tailWord_7354111, baseEnd_7354111] using wordTrace_append hprefix tailTrace_7354111
  have hstable : (prefixWord ++ tailWord_7354111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354111).length < 2 ^ (prefixWord ++ tailWord_7354111).sum := by decide
  have hdescent : baseEnd_7354111 < baseStart_7354111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354122 : List Nat := [3, 1, 2, 2, 1, 3, 4, 1, 2, 2, 2]
def baseStart_7354122 : Nat := 118140960795 + 7354122 * 2 ^ 59
def prefixEnd_7354122 : Nat := 4983230072969 + 3 ^ 40 * 7354122 * 2
def baseEnd_7354122 : Nat := 3776199377804181197554015

theorem tailTrace_7354122 : CollatzResearch.WordTrace tailWord_7354122 prefixEnd_7354122 3776199377804181197554015 := by
  unfold tailWord_7354122
  simp only [CollatzResearch.WordTrace]
  refine ⟨67056716265819863222178155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178817910042186301925808413 67056716265819863222178155)
  ·
    refine ⟨100585074398729794833267233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67056716265819863222178155 100585074398729794833267233)
    ·
      refine ⟨75438805799047346124950425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100585074398729794833267233 75438805799047346124950425)
      ·
        refine ⟨56579104349285509593712819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75438805799047346124950425 56579104349285509593712819)
        ·
          refine ⟨84868656523928264390569229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56579104349285509593712819 84868656523928264390569229)
          ·
            refine ⟨31825746196473099146463461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84868656523928264390569229 31825746196473099146463461)
            ·
              refine ⟨5967327411838706089961899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31825746196473099146463461 5967327411838706089961899)
              ·
                refine ⟨8950991117758059134942849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5967327411838706089961899 8950991117758059134942849)
                ·
                  refine ⟨6713243338318544351207137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8950991117758059134942849 6713243338318544351207137)
                  ·
                    refine ⟨5034932503738908263405353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6713243338318544351207137 5034932503738908263405353)
                    ·
                      refine ⟨3776199377804181197554015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034932503738908263405353 3776199377804181197554015)
                      ·
                        rfl

theorem cell23_7354122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_7354122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354122 prefixEnd_7354122 := by exact prefixLift 7354122
  have htrace : WordTrace (prefixWord ++ tailWord_7354122) baseStart_7354122 baseEnd_7354122 := by
    simpa [prefixWord, tailWord_7354122, baseEnd_7354122] using wordTrace_append hprefix tailTrace_7354122
  have hstable : (prefixWord ++ tailWord_7354122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354122).length < 2 ^ (prefixWord ++ tailWord_7354122).sum := by decide
  have hdescent : baseEnd_7354122 < baseStart_7354122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354124 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 3, 7]
def baseStart_7354124 : Nat := 118140960795 + 7354124 * 2 ^ 59
def prefixEnd_7354124 : Nat := 4983230072969 + 3 ^ 40 * 7354124 * 2
def baseEnd_7354124 : Nat := 1258733468255163396576335

theorem tailTrace_7354124 : CollatzResearch.WordTrace tailWord_7354124 prefixEnd_7354124 1258733468255163396576335 := by
  unfold tailWord_7354124
  simp only [CollatzResearch.WordTrace]
  refine ⟨134113469004636103615142713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178817958672848138153523617 134113469004636103615142713)
  ·
    refine ⟨100585101753477077711357035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134113469004636103615142713 100585101753477077711357035)
    ·
      refine ⟨150877652630215616567035553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100585101753477077711357035 150877652630215616567035553)
      ·
        refine ⟨113158239472661712425276665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150877652630215616567035553 113158239472661712425276665)
        ·
          refine ⟨84868679604496284318957499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113158239472661712425276665 84868679604496284318957499)
          ·
            refine ⟨127303019406744426478436249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84868679604496284318957499 127303019406744426478436249)
            ·
              refine ⟨95477264555058319858827187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127303019406744426478436249 95477264555058319858827187)
              ·
                refine ⟨143215896832587479788240781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95477264555058319858827187 143215896832587479788240781)
                ·
                  refine ⟨53705961312220304920590293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143215896832587479788240781 53705961312220304920590293)
                  ·
                    refine ⟨1258733468255163396576335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53705961312220304920590293 1258733468255163396576335)
                    ·
                      rfl

theorem cell23_7354124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_7354124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354124 prefixEnd_7354124 := by exact prefixLift 7354124
  have htrace : WordTrace (prefixWord ++ tailWord_7354124) baseStart_7354124 baseEnd_7354124 := by
    simpa [prefixWord, tailWord_7354124, baseEnd_7354124] using wordTrace_append hprefix tailTrace_7354124
  have hstable : (prefixWord ++ tailWord_7354124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354124).length < 2 ^ (prefixWord ++ tailWord_7354124).sum := by decide
  have hdescent : baseEnd_7354124 < baseStart_7354124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354131 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 4, 5, 2]
def baseStart_7354131 : Nat := 118140960795 + 7354131 * 2 ^ 59
def prefixEnd_7354131 : Nat := 4983230072969 + 3 ^ 40 * 7354131 * 2
def baseEnd_7354131 : Nat := 3776203999130071662341473

theorem tailTrace_7354131 : CollatzResearch.WordTrace tailWord_7354131 prefixEnd_7354131 3776203999130071662341473 := by
  unfold tailWord_7354131
  simp only [CollatzResearch.WordTrace]
  refine ⟨268227193320246847425790247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178818128880164564950526831 268227193320246847425790247)
  ·
    refine ⟨402340789980370271138685371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268227193320246847425790247 402340789980370271138685371)
    ·
      refine ⟨603511184970555406708028057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402340789980370271138685371 603511184970555406708028057)
      ·
        refine ⟨452633388727916555031021043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 603511184970555406708028057 452633388727916555031021043)
        ·
          refine ⟨678950083091874832546531565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452633388727916555031021043 678950083091874832546531565)
          ·
            refine ⟨254606281159453062204949337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 678950083091874832546531565 254606281159453062204949337)
            ·
              refine ⟨190954710869589796653712003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254606281159453062204949337 190954710869589796653712003)
              ·
                refine ⟨286432066304384694980568005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190954710869589796653712003 286432066304384694980568005)
                ·
                  refine ⟨53706012432072130308856501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286432066304384694980568005 53706012432072130308856501)
                  ·
                    refine ⟨5034938665506762216455297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53706012432072130308856501 5034938665506762216455297)
                    ·
                      refine ⟨3776203999130071662341473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5034938665506762216455297 3776203999130071662341473)
                      ·
                        rfl

theorem cell23_7354131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 5, 2].length) (baseStart_7354131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354131 prefixEnd_7354131 := by exact prefixLift 7354131
  have htrace : WordTrace (prefixWord ++ tailWord_7354131) baseStart_7354131 baseEnd_7354131 := by
    simpa [prefixWord, tailWord_7354131, baseEnd_7354131] using wordTrace_append hprefix tailTrace_7354131
  have hstable : (prefixWord ++ tailWord_7354131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354131).length < 2 ^ (prefixWord ++ tailWord_7354131).sum := by decide
  have hdescent : baseEnd_7354131 < baseStart_7354131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354181 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 1, 4, 3]
def baseStart_7354181 : Nat := 118140960795 + 7354181 * 2 ^ 59
def prefixEnd_7354181 : Nat := 4983230072969 + 3 ^ 40 * 7354181 * 2
def baseEnd_7354181 : Nat := 3776229673162796466716243

theorem tailTrace_7354181 : CollatzResearch.WordTrace tailWord_7354181 prefixEnd_7354181 3776229673162796466716243 := by
  unfold tailWord_7354181
  simp only [CollatzResearch.WordTrace]
  refine ⟨268229016970065705965110397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178819344646710470643406931 268229016970065705965110397)
  ·
    refine ⟨100585881363774639736916399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268229016970065705965110397 100585881363774639736916399)
    ·
      refine ⟨150878822045661959605374599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100585881363774639736916399 150878822045661959605374599)
      ·
        refine ⟨226318233068492939408061899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150878822045661959605374599 226318233068492939408061899)
        ·
          refine ⟨339477349602739409112092849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226318233068492939408061899 339477349602739409112092849)
          ·
            refine ⟨254608012202054556834069637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339477349602739409112092849 254608012202054556834069637)
            ·
              refine ⟨47739002287885229406388057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254608012202054556834069637 47739002287885229406388057)
              ·
                refine ⟨35804251715913922054791043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47739002287885229406388057 35804251715913922054791043)
                ·
                  refine ⟨53706377573870883082186565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35804251715913922054791043 53706377573870883082186565)
                  ·
                    refine ⟨10069945795100790577909981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53706377573870883082186565 10069945795100790577909981)
                    ·
                      refine ⟨3776229673162796466716243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10069945795100790577909981 3776229673162796466716243)
                      ·
                        rfl

theorem cell23_7354181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_7354181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354181 prefixEnd_7354181 := by exact prefixLift 7354181
  have htrace : WordTrace (prefixWord ++ tailWord_7354181) baseStart_7354181 baseEnd_7354181 := by
    simpa [prefixWord, tailWord_7354181, baseEnd_7354181] using wordTrace_append hprefix tailTrace_7354181
  have hstable : (prefixWord ++ tailWord_7354181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354181).length < 2 ^ (prefixWord ++ tailWord_7354181).sum := by decide
  have hdescent : baseEnd_7354181 < baseStart_7354181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354221 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_7354221 : Nat := 118140960795 + 7354221 * 2 ^ 59
def prefixEnd_7354221 : Nat := 4983230072969 + 3 ^ 40 * 7354221 * 2
def baseEnd_7354221 : Nat := 3776250212388976310216059

theorem tailTrace_7354221 : CollatzResearch.WordTrace tailWord_7354221 prefixEnd_7354221 3776250212388976310216059 := by
  unfold tailWord_7354221
  simp only [CollatzResearch.WordTrace]
  refine ⟨268230475889920792796566517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178820317259947195197711011 268230475889920792796566517)
  ·
    refine ⟨25146607114680074324678111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268230475889920792796566517 25146607114680074324678111)
    ·
      refine ⟨37719910672020111487017167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25146607114680074324678111 37719910672020111487017167)
      ·
        refine ⟨56579866008030167230525751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37719910672020111487017167 56579866008030167230525751)
        ·
          refine ⟨84869799012045250845788627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56579866008030167230525751 84869799012045250845788627)
          ·
            refine ⟨127304698518067876268682941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84869799012045250845788627 127304698518067876268682941)
            ·
              refine ⟨47739261944275453600756103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127304698518067876268682941 47739261944275453600756103)
              ·
                refine ⟨71608892916413180401134155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47739261944275453600756103 71608892916413180401134155)
                ·
                  refine ⟨107413339374619770601701233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71608892916413180401134155 107413339374619770601701233)
                  ·
                    refine ⟨80560004530964827951275925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107413339374619770601701233 80560004530964827951275925)
                    ·
                      refine ⟨3776250212388976310216059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80560004530964827951275925 3776250212388976310216059)
                      ·
                        rfl

theorem cell23_7354221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_7354221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354221 prefixEnd_7354221 := by exact prefixLift 7354221
  have htrace : WordTrace (prefixWord ++ tailWord_7354221) baseStart_7354221 baseEnd_7354221 := by
    simpa [prefixWord, tailWord_7354221, baseEnd_7354221] using wordTrace_append hprefix tailTrace_7354221
  have hstable : (prefixWord ++ tailWord_7354221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354221).length < 2 ^ (prefixWord ++ tailWord_7354221).sum := by decide
  have hdescent : baseEnd_7354221 < baseStart_7354221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354222 : List Nat := [4, 1, 2, 3, 1, 1, 2, 4, 1, 4]
def baseStart_7354222 : Nat := 118140960795 + 7354222 * 2 ^ 59
def prefixEnd_7354222 : Nat := 4983230072969 + 3 ^ 40 * 7354222 * 2
def baseEnd_7354222 : Nat := 1258750241956543602101185

theorem tailTrace_7354222 : CollatzResearch.WordTrace tailWord_7354222 prefixEnd_7354222 1258750241956543602101185 := by
  unfold tailWord_7354222
  simp only [CollatzResearch.WordTrace]
  refine ⟨33528814045364646245919115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178820341575278113311568613 33528814045364646245919115)
  ·
    refine ⟨50293221068046969368878673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33528814045364646245919115 50293221068046969368878673)
    ·
      refine ⟨37719915801035227026659005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50293221068046969368878673 37719915801035227026659005)
      ·
        refine ⟨14144968425388210134997127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37719915801035227026659005 14144968425388210134997127)
        ·
          refine ⟨21217452638082315202495691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14144968425388210134997127 21217452638082315202495691)
          ·
            refine ⟨31826178957123472803743537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21217452638082315202495691 31826178957123472803743537)
            ·
              refine ⟨23869634217842604602807653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31826178957123472803743537 23869634217842604602807653)
              ·
                refine ⟨4475556415845488363026435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23869634217842604602807653 4475556415845488363026435)
                ·
                  refine ⟨6713334623768232544539653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4475556415845488363026435 6713334623768232544539653)
                  ·
                    refine ⟨1258750241956543602101185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6713334623768232544539653 1258750241956543602101185)
                    ·
                      rfl

theorem cell23_7354222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_7354222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354222 prefixEnd_7354222 := by exact prefixLift 7354222
  have htrace : WordTrace (prefixWord ++ tailWord_7354222) baseStart_7354222 baseEnd_7354222 := by
    simpa [prefixWord, tailWord_7354222, baseEnd_7354222] using wordTrace_append hprefix tailTrace_7354222
  have hstable : (prefixWord ++ tailWord_7354222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354222).length < 2 ^ (prefixWord ++ tailWord_7354222).sum := by decide
  have hdescent : baseEnd_7354222 < baseStart_7354222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354261 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 3, 6]
def baseStart_7354261 : Nat := 118140960795 + 7354261 * 2 ^ 59
def prefixEnd_7354261 : Nat := 4983230072969 + 3 ^ 40 * 7354261 * 2
def baseEnd_7354261 : Nat := 1258756917205052051238625

theorem tailTrace_7354261 : CollatzResearch.WordTrace tailWord_7354261 prefixEnd_7354261 1258756917205052051238625 := by
  unfold tailWord_7354261
  simp only [CollatzResearch.WordTrace]
  refine ⟨268231934809775879628022637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178821289873183919752015091 268231934809775879628022637)
  ·
    refine ⟨100586975553665954860508489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268231934809775879628022637 100586975553665954860508489)
    ·
      refine ⟨75440231665249466145381367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100586975553665954860508489 75440231665249466145381367)
      ·
        refine ⟨113160347497874199218072051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75440231665249466145381367 113160347497874199218072051)
        ·
          refine ⟨169740521246811298827108077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113160347497874199218072051 169740521246811298827108077)
          ·
            refine ⟨63652695467554237060165529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169740521246811298827108077 63652695467554237060165529)
            ·
              refine ⟨47739521600665677795124147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63652695467554237060165529 47739521600665677795124147)
              ·
                refine ⟨71609282400998516692686221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47739521600665677795124147 71609282400998516692686221)
                ·
                  refine ⟨26853480900374443759757333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71609282400998516692686221 26853480900374443759757333)
                  ·
                    refine ⟨1258756917205052051238625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26853480900374443759757333 1258756917205052051238625)
                    ·
                      rfl

theorem cell23_7354261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_7354261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354261 prefixEnd_7354261 := by exact prefixLift 7354261
  have htrace : WordTrace (prefixWord ++ tailWord_7354261) baseStart_7354261 baseEnd_7354261 := by
    simpa [prefixWord, tailWord_7354261, baseEnd_7354261] using wordTrace_append hprefix tailTrace_7354261
  have hstable : (prefixWord ++ tailWord_7354261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354261).length < 2 ^ (prefixWord ++ tailWord_7354261).sum := by decide
  have hdescent : baseEnd_7354261 < baseStart_7354261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354281 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 5, 2, 4]
def baseStart_7354281 : Nat := 118140960795 + 7354281 * 2 ^ 59
def prefixEnd_7354281 : Nat := 4983230072969 + 3 ^ 40 * 7354281 * 2
def baseEnd_7354281 : Nat := 3776281021228246075465783

theorem tailTrace_7354281 : CollatzResearch.WordTrace tailWord_7354281 prefixEnd_7354281 3776281021228246075465783 := by
  unfold tailWord_7354281
  simp only [CollatzResearch.WordTrace]
  refine ⟨268232664269703423043750697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178821776179802282029167131 268232664269703423043750697)
  ·
    refine ⟨201174498202277567282813023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268232664269703423043750697 201174498202277567282813023)
    ·
      refine ⟨301761747303416350924219535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201174498202277567282813023 301761747303416350924219535)
      ·
        refine ⟨452642620955124526386329303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301761747303416350924219535 452642620955124526386329303)
        ·
          refine ⟨678963931432686789579493955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452642620955124526386329303 678963931432686789579493955)
          ·
            refine ⟨1018445897149030184369240933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678963931432686789579493955 1018445897149030184369240933)
            ·
              refine ⟨190958605715443159569232675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1018445897149030184369240933 190958605715443159569232675)
              ·
                refine ⟨286437908573164739353849013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190958605715443159569232675 286437908573164739353849013)
                ·
                  refine ⟨26853553928734194314423345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286437908573164739353849013 26853553928734194314423345)
                  ·
                    refine ⟨20140165446550645735817509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26853553928734194314423345 20140165446550645735817509)
                    ·
                      refine ⟨3776281021228246075465783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20140165446550645735817509 3776281021228246075465783)
                      ·
                        rfl

theorem cell23_7354281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_7354281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354281 prefixEnd_7354281 := by exact prefixLift 7354281
  have htrace : WordTrace (prefixWord ++ tailWord_7354281) baseStart_7354281 baseEnd_7354281 := by
    simpa [prefixWord, tailWord_7354281, baseEnd_7354281] using wordTrace_append hprefix tailTrace_7354281
  have hstable : (prefixWord ++ tailWord_7354281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354281).length < 2 ^ (prefixWord ++ tailWord_7354281).sum := by decide
  have hdescent : baseEnd_7354281 < baseStart_7354281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354286 : List Nat := [4, 1, 5, 1, 1, 2, 2, 1, 6]
def baseStart_7354286 : Nat := 118140960795 + 7354286 * 2 ^ 59
def prefixEnd_7354286 : Nat := 4983230072969 + 3 ^ 40 * 7354286 * 2
def baseEnd_7354286 : Nat := 419587065403502061767029

theorem tailTrace_7354286 : CollatzResearch.WordTrace tailWord_7354286 prefixEnd_7354286 419587065403502061767029 := by
  unfold tailWord_7354286
  simp only [CollatzResearch.WordTrace]
  refine ⟨33529105829335663612210339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178821897756456872598455141 33529105829335663612210339)
  ·
    refine ⟨50293658744003495418315509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33529105829335663612210339 50293658744003495418315509)
    ·
      refine ⟨4715030507250327695467079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50293658744003495418315509 4715030507250327695467079)
      ·
        refine ⟨7072545760875491543200619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4715030507250327695467079 7072545760875491543200619)
        ·
          refine ⟨10608818641313237314800929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7072545760875491543200619 10608818641313237314800929)
          ·
            refine ⟨7956613980984927986100697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10608818641313237314800929 7956613980984927986100697)
            ·
              refine ⟨5967460485738695989575523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7956613980984927986100697 5967460485738695989575523)
              ·
                refine ⟨8951190728608043984363285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5967460485738695989575523 8951190728608043984363285)
                ·
                  refine ⟨419587065403502061767029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8951190728608043984363285 419587065403502061767029)
                  ·
                    rfl

theorem cell23_7354286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_7354286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354286 prefixEnd_7354286 := by exact prefixLift 7354286
  have htrace : WordTrace (prefixWord ++ tailWord_7354286) baseStart_7354286 baseEnd_7354286 := by
    simpa [prefixWord, tailWord_7354286, baseEnd_7354286] using wordTrace_append hprefix tailTrace_7354286
  have hstable : (prefixWord ++ tailWord_7354286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354286).length < 2 ^ (prefixWord ++ tailWord_7354286).sum := by decide
  have hdescent : baseEnd_7354286 < baseStart_7354286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354291 : List Nat := [1, 1, 1, 2, 3, 1, 6, 8]
def baseStart_7354291 : Nat := 118140960795 + 7354291 * 2 ^ 59
def prefixEnd_7354291 : Nat := 4983230072969 + 3 ^ 40 * 7354291 * 2
def baseEnd_7354291 : Nat := 139862450223510779123731

theorem tailTrace_7354291 : CollatzResearch.WordTrace tailWord_7354291 prefixEnd_7354291 139862450223510779123731 := by
  unfold tailWord_7354291
  simp only [CollatzResearch.WordTrace]
  refine ⟨268233028999667194751614727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178822019333111463167743151 268233028999667194751614727)
  ·
    refine ⟨402349543499500792127422091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268233028999667194751614727 402349543499500792127422091)
    ·
      refine ⟨603524315249251188191133137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402349543499500792127422091 603524315249251188191133137)
      ·
        refine ⟨452643236436938391143349853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 603524315249251188191133137 452643236436938391143349853)
        ·
          refine ⟨169741213663851896678756195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 452643236436938391143349853 169741213663851896678756195)
          ·
            refine ⟨254611820495777845018134293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169741213663851896678756195 254611820495777845018134293)
            ·
              refine ⟨11934929085739586485225045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 254611820495777845018134293 11934929085739586485225045)
              ·
                refine ⟨139862450223510779123731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11934929085739586485225045 139862450223510779123731)
                ·
                  rfl

theorem cell23_7354291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 8].length) (baseStart_7354291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354291 prefixEnd_7354291 := by exact prefixLift 7354291
  have htrace : WordTrace (prefixWord ++ tailWord_7354291) baseStart_7354291 baseEnd_7354291 := by
    simpa [prefixWord, tailWord_7354291, baseEnd_7354291] using wordTrace_append hprefix tailTrace_7354291
  have hstable : (prefixWord ++ tailWord_7354291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354291).length < 2 ^ (prefixWord ++ tailWord_7354291).sum := by decide
  have hdescent : baseEnd_7354291 < baseStart_7354291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354302 : List Nat := [4, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_7354302 : Nat := 118140960795 + 7354302 * 2 ^ 59
def prefixEnd_7354302 : Nat := 4983230072969 + 3 ^ 40 * 7354302 * 2
def baseEnd_7354302 : Nat := 3776291804321990493303187

theorem tailTrace_7354302 : CollatzResearch.WordTrace tailWord_7354302 prefixEnd_7354302 3776291804321990493303187 := by
  unfold tailWord_7354302
  simp only [CollatzResearch.WordTrace]
  refine ⟨33529178775328417953783145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178822286801751562420176773 33529178775328417953783145)
  ·
    refine ⟨25146884081496313465337359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33529178775328417953783145 25146884081496313465337359)
    ·
      refine ⟨37720326122244470198006039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25146884081496313465337359 37720326122244470198006039)
      ·
        refine ⟨56580489183366705297009059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37720326122244470198006039 56580489183366705297009059)
        ·
          refine ⟨84870733775050057945513589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56580489183366705297009059 84870733775050057945513589)
          ·
            refine ⟨7956631291410942932391899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84870733775050057945513589 7956631291410942932391899)
            ·
              refine ⟨11934946937116414398587849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7956631291410942932391899 11934946937116414398587849)
              ·
                refine ⟨8951210202837310798940887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11934946937116414398587849 8951210202837310798940887)
                ·
                  refine ⟨13426815304255966198411331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8951210202837310798940887 13426815304255966198411331)
                  ·
                    refine ⟨20140222956383949297616997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13426815304255966198411331 20140222956383949297616997)
                    ·
                      refine ⟨3776291804321990493303187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20140222956383949297616997 3776291804321990493303187)
                      ·
                        rfl

theorem cell23_7354302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_7354302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354302 prefixEnd_7354302 := by exact prefixLift 7354302
  have htrace : WordTrace (prefixWord ++ tailWord_7354302) baseStart_7354302 baseEnd_7354302 := by
    simpa [prefixWord, tailWord_7354302, baseEnd_7354302] using wordTrace_append hprefix tailTrace_7354302
  have hstable : (prefixWord ++ tailWord_7354302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354302).length < 2 ^ (prefixWord ++ tailWord_7354302).sum := by decide
  have hdescent : baseEnd_7354302 < baseStart_7354302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354322 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_7354322 : Nat := 118140960795 + 7354322 * 2 ^ 59
def prefixEnd_7354322 : Nat := 4983230072969 + 3 ^ 40 * 7354322 * 2
def baseEnd_7354322 : Nat := 3776302073935080415053095

theorem tailTrace_7354322 : CollatzResearch.WordTrace tailWord_7354322 prefixEnd_7354322 3776302073935080415053095 := by
  unfold tailWord_7354322
  simp only [CollatzResearch.WordTrace]
  refine ⟨67058539915638721761498305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178822773108369924697328813 67058539915638721761498305)
  ·
    refine ⟨50293904936729041321123729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67058539915638721761498305 50293904936729041321123729)
    ·
      refine ⟨37720428702546780990842797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50293904936729041321123729 37720428702546780990842797)
      ·
        refine ⟨14145160763455042871566049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37720428702546780990842797 14145160763455042871566049)
        ·
          refine ⟨10608870572591282153674537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14145160763455042871566049 10608870572591282153674537)
          ·
            refine ⟨7956652929443461615255903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10608870572591282153674537 7956652929443461615255903)
            ·
              refine ⟨11934979394165192422883855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7956652929443461615255903 11934979394165192422883855)
              ·
                refine ⟨17902469091247788634325783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11934979394165192422883855 17902469091247788634325783)
                ·
                  refine ⟨26853703636871682951488675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17902469091247788634325783 26853703636871682951488675)
                  ·
                    refine ⟨40280555455307524427233013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26853703636871682951488675 40280555455307524427233013)
                    ·
                      refine ⟨3776302073935080415053095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40280555455307524427233013 3776302073935080415053095)
                      ·
                        rfl

theorem cell23_7354322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_7354322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354322 prefixEnd_7354322 := by exact prefixLift 7354322
  have htrace : WordTrace (prefixWord ++ tailWord_7354322) baseStart_7354322 baseEnd_7354322 := by
    simpa [prefixWord, tailWord_7354322, baseEnd_7354322] using wordTrace_append hprefix tailTrace_7354322
  have hstable : (prefixWord ++ tailWord_7354322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354322).length < 2 ^ (prefixWord ++ tailWord_7354322).sum := by decide
  have hdescent : baseEnd_7354322 < baseStart_7354322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354392 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 4, 2, 2]
def baseStart_7354392 : Nat := 118140960795 + 7354392 * 2 ^ 59
def prefixEnd_7354392 : Nat := 4983230072969 + 3 ^ 40 * 7354392 * 2
def baseEnd_7354392 : Nat := 3776338017580895141177773

theorem tailTrace_7354392 : CollatzResearch.WordTrace tailWord_7354392 prefixEnd_7354392 3776338017580895141177773 := by
  unfold tailWord_7354392
  simp only [CollatzResearch.WordTrace]
  refine ⟨134118356386150644500520715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178824475181534192667360953 134118356386150644500520715)
  ·
    refine ⟨201177534579225966750781073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134118356386150644500520715 201177534579225966750781073)
    ·
      refine ⟨150883150934419475063085805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201177534579225966750781073 150883150934419475063085805)
      ·
        refine ⟨56581181600407303148657177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150883150934419475063085805 56581181600407303148657177)
        ·
          refine ⟨42435886200305477361492883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56581181600407303148657177 42435886200305477361492883)
          ·
            refine ⟨63653829300458216042239325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42435886200305477361492883 63653829300458216042239325)
            ·
              refine ⟨23870185987671831015839747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63653829300458216042239325 23870185987671831015839747)
              ·
                refine ⟨35805278981507746523759621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23870185987671831015839747 35805278981507746523759621)
                ·
                  refine ⟨6713489809032702473204929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35805278981507746523759621 6713489809032702473204929)
                  ·
                    refine ⟨5035117356774526854903697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6713489809032702473204929 5035117356774526854903697)
                    ·
                      refine ⟨3776338017580895141177773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5035117356774526854903697 3776338017580895141177773)
                      ·
                        rfl

theorem cell23_7354392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_7354392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354392 prefixEnd_7354392 := by exact prefixLift 7354392
  have htrace : WordTrace (prefixWord ++ tailWord_7354392) baseStart_7354392 baseEnd_7354392 := by
    simpa [prefixWord, tailWord_7354392, baseEnd_7354392] using wordTrace_append hprefix tailTrace_7354392
  have hstable : (prefixWord ++ tailWord_7354392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354392).length < 2 ^ (prefixWord ++ tailWord_7354392).sum := by decide
  have hdescent : baseEnd_7354392 < baseStart_7354392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354428 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 1, 7]
def baseStart_7354428 : Nat := 118140960795 + 7354428 * 2 ^ 59
def prefixEnd_7354428 : Nat := 4983230072969 + 3 ^ 40 * 7354428 * 2
def baseEnd_7354428 : Nat := 1258785500961485666775869

theorem tailTrace_7354428 : CollatzResearch.WordTrace tailWord_7354428 prefixEnd_7354428 1258785500961485666775869 := by
  unfold tailWord_7354428
  simp only [CollatzResearch.WordTrace]
  refine ⟨134119012900085433574675969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178825350533447244766234625 134119012900085433574675969)
  ·
    refine ⟨100589259675064075181006977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134119012900085433574675969 100589259675064075181006977)
    ·
      refine ⟨75441944756298056385755233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100589259675064075181006977 75441944756298056385755233)
      ·
        refine ⟨56581458567223542289316425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75441944756298056385755233 56581458567223542289316425)
        ·
          refine ⟨42436093925417656716987319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56581458567223542289316425 42436093925417656716987319)
          ·
            refine ⟨63654140888126485075480979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42436093925417656716987319 63654140888126485075480979)
            ·
              refine ⟨95481211332189727613221469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63654140888126485075480979 95481211332189727613221469)
              ·
                refine ⟨35805454249571147854958051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95481211332189727613221469 35805454249571147854958051)
                ·
                  refine ⟨53708181374356721782437077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35805454249571147854958051 53708181374356721782437077)
                  ·
                    refine ⟨1258785500961485666775869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53708181374356721782437077 1258785500961485666775869)
                    ·
                      rfl

theorem cell23_7354428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_7354428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354428 prefixEnd_7354428 := by exact prefixLift 7354428
  have htrace : WordTrace (prefixWord ++ tailWord_7354428) baseStart_7354428 baseEnd_7354428 := by
    simpa [prefixWord, tailWord_7354428, baseEnd_7354428] using wordTrace_append hprefix tailTrace_7354428
  have hstable : (prefixWord ++ tailWord_7354428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354428).length < 2 ^ (prefixWord ++ tailWord_7354428).sum := by decide
  have hdescent : baseEnd_7354428 < baseStart_7354428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354432 : List Nat := [2, 1, 1, 2, 2, 6, 1, 3, 5]
def baseStart_7354432 : Nat := 118140960795 + 7354432 * 2 ^ 59
def prefixEnd_7354432 : Nat := 4983230072969 + 3 ^ 40 * 7354432 * 2
def baseEnd_7354432 : Nat := 419595395200786109408621

theorem tailTrace_7354432 : CollatzResearch.WordTrace tailWord_7354432 prefixEnd_7354432 419595395200786109408621 := by
  unfold tailWord_7354432
  simp only [CollatzResearch.WordTrace]
  refine ⟨134119085846078187916248775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178825447794770917221665033 134119085846078187916248775)
  ·
    refine ⟨201178628769117281874373163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134119085846078187916248775 201178628769117281874373163)
    ·
      refine ⟨301767943153675922811559745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201178628769117281874373163 301767943153675922811559745)
      ·
        refine ⟨226325957365256942108669809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301767943153675922811559745 226325957365256942108669809)
        ·
          refine ⟨169744468023942706581502357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226325957365256942108669809 169744468023942706581502357)
          ·
            refine ⟨7956771938622314371007923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 169744468023942706581502357 7956771938622314371007923)
            ·
              refine ⟨11935157907933471556511885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7956771938622314371007923 11935157907933471556511885)
              ·
                refine ⟨4475684215475051833691957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11935157907933471556511885 4475684215475051833691957)
                ·
                  refine ⟨419595395200786109408621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4475684215475051833691957 419595395200786109408621)
                  ·
                    rfl

theorem cell23_7354432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 5].length) (baseStart_7354432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354432 prefixEnd_7354432 := by exact prefixLift 7354432
  have htrace : WordTrace (prefixWord ++ tailWord_7354432) baseStart_7354432 baseEnd_7354432 := by
    simpa [prefixWord, tailWord_7354432, baseEnd_7354432] using wordTrace_append hprefix tailTrace_7354432
  have hstable : (prefixWord ++ tailWord_7354432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354432).length < 2 ^ (prefixWord ++ tailWord_7354432).sum := by decide
  have hdescent : baseEnd_7354432 < baseStart_7354432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354465 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 1, 6, 2]
def baseStart_7354465 : Nat := 118140960795 + 7354465 * 2 ^ 59
def prefixEnd_7354465 : Nat := 4983230072969 + 3 ^ 40 * 7354465 * 2
def baseEnd_7354465 : Nat := 3776375501668673355564937

theorem tailTrace_7354465 : CollatzResearch.WordTrace tailWord_7354465 prefixEnd_7354465 3776375501668673355564937 := by
  unfold tailWord_7354465
  simp only [CollatzResearch.WordTrace]
  refine ⟨268239375301036822468448849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178826250200691214978965899 268239375301036822468448849)
  ·
    refine ⟨201179531475777616851336637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268239375301036822468448849 201179531475777616851336637)
    ·
      refine ⟨75442324303416606319251239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201179531475777616851336637 75442324303416606319251239)
      ·
        refine ⟨113163486455124909478876859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75442324303416606319251239 113163486455124909478876859)
        ·
          refine ⟨169745229682687364218315289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113163486455124909478876859 169745229682687364218315289)
          ·
            refine ⟨127308922262015523163736467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169745229682687364218315289 127308922262015523163736467)
            ·
              refine ⟨190963383393023284745604701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127308922262015523163736467 190963383393023284745604701)
              ·
                refine ⟨71611268772383731779601763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190963383393023284745604701 71611268772383731779601763)
                ·
                  refine ⟨107416903158575597669402645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71611268772383731779601763 107416903158575597669402645)
                  ·
                    refine ⟨5035167335558231140753249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107416903158575597669402645 5035167335558231140753249)
                    ·
                      refine ⟨3776375501668673355564937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5035167335558231140753249 3776375501668673355564937)
                      ·
                        rfl

theorem cell23_7354465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_7354465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354465 prefixEnd_7354465 := by exact prefixLift 7354465
  have htrace : WordTrace (prefixWord ++ tailWord_7354465) baseStart_7354465 baseEnd_7354465 := by
    simpa [prefixWord, tailWord_7354465, baseEnd_7354465] using wordTrace_append hprefix tailTrace_7354465
  have hstable : (prefixWord ++ tailWord_7354465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354465).length < 2 ^ (prefixWord ++ tailWord_7354465).sum := by decide
  have hdescent : baseEnd_7354465 < baseStart_7354465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354482 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_7354482 : Nat := 118140960795 + 7354482 * 2 ^ 59
def prefixEnd_7354482 : Nat := 4983230072969 + 3 ^ 40 * 7354482 * 2
def baseEnd_7354482 : Nat := 3776384230839799789052359

theorem tailTrace_7354482 : CollatzResearch.WordTrace tailWord_7354482 prefixEnd_7354482 3776384230839799789052359 := by
  unfold tailWord_7354482
  simp only [CollatzResearch.WordTrace]
  refine ⟨67059998835493808592954425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178826663561316822914545133 67059998835493808592954425)
  ·
    refine ⟨50294999126620356444715819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67059998835493808592954425 50294999126620356444715819)
    ·
      refine ⟨75442498689930534667073729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50294999126620356444715819 75442498689930534667073729)
      ·
        refine ⟨56581874017447901000305297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75442498689930534667073729 56581874017447901000305297)
        ·
          refine ⟨42436405513085925750228973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56581874017447901000305297 42436405513085925750228973)
          ·
            refine ⟨15913652067407222156335865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42436405513085925750228973 15913652067407222156335865)
            ·
              refine ⟨11935239050555416617251899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15913652067407222156335865 11935239050555416617251899)
              ·
                refine ⟨17902858575833124925877849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11935239050555416617251899 17902858575833124925877849)
                ·
                  refine ⟨13427143931874843694408387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17902858575833124925877849 13427143931874843694408387)
                  ·
                    refine ⟨20140715897812265541612581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13427143931874843694408387 20140715897812265541612581)
                    ·
                      refine ⟨3776384230839799789052359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20140715897812265541612581 3776384230839799789052359)
                      ·
                        rfl

theorem cell23_7354482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_7354482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354482 prefixEnd_7354482 := by exact prefixLift 7354482
  have htrace : WordTrace (prefixWord ++ tailWord_7354482) baseStart_7354482 baseEnd_7354482 := by
    simpa [prefixWord, tailWord_7354482, baseEnd_7354482] using wordTrace_append hprefix tailTrace_7354482
  have hstable : (prefixWord ++ tailWord_7354482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354482).length < 2 ^ (prefixWord ++ tailWord_7354482).sum := by decide
  have hdescent : baseEnd_7354482 < baseStart_7354482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354505 : List Nat := [1, 2, 1, 1, 4, 2, 4, 2, 6]
def baseStart_7354505 : Nat := 118140960795 + 7354505 * 2 ^ 59
def prefixEnd_7354505 : Nat := 4983230072969 + 3 ^ 40 * 7354505 * 2
def baseEnd_7354505 : Nat := 419599560099428133229417

theorem tailTrace_7354505 : CollatzResearch.WordTrace tailWord_7354505 prefixEnd_7354505 419599560099428133229417 := by
  unfold tailWord_7354505
  simp only [CollatzResearch.WordTrace]
  refine ⟨268240834220891909299904969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178827222813927939533269979 268240834220891909299904969)
  ·
    refine ⟨201180625665668931974928727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268240834220891909299904969 201180625665668931974928727)
    ·
      refine ⟨301770938498503397962393091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201180625665668931974928727 301770938498503397962393091)
      ·
        refine ⟨452656407747755096943589637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301770938498503397962393091 452656407747755096943589637)
        ·
          refine ⟨84873076452704080676923057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 452656407747755096943589637 84873076452704080676923057)
          ·
            refine ⟨63654807339528060507692293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84873076452704080676923057 63654807339528060507692293)
            ·
              refine ⟨11935276376161511345192305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63654807339528060507692293 11935276376161511345192305)
              ·
                refine ⟨8951457282121133508894229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11935276376161511345192305 8951457282121133508894229)
                ·
                  refine ⟨419599560099428133229417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8951457282121133508894229 419599560099428133229417)
                  ·
                    rfl

theorem cell23_7354505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 6].length) (baseStart_7354505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354505 prefixEnd_7354505 := by exact prefixLift 7354505
  have htrace : WordTrace (prefixWord ++ tailWord_7354505) baseStart_7354505 baseEnd_7354505 := by
    simpa [prefixWord, tailWord_7354505, baseEnd_7354505] using wordTrace_append hprefix tailTrace_7354505
  have hstable : (prefixWord ++ tailWord_7354505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354505).length < 2 ^ (prefixWord ++ tailWord_7354505).sum := by decide
  have hdescent : baseEnd_7354505 < baseStart_7354505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354516 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_7354516 : Nat := 118140960795 + 7354516 * 2 ^ 59
def prefixEnd_7354516 : Nat := 4983230072969 + 3 ^ 40 * 7354516 * 2
def baseEnd_7354516 : Nat := 3776401689182052656027203

theorem tailTrace_7354516 : CollatzResearch.WordTrace tailWord_7354516 prefixEnd_7354516 3776401689182052656027203 := by
  unfold tailWord_7354516
  simp only [CollatzResearch.WordTrace]
  refine ⟨134120617711926029089277701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178827490282568038785703601 134120617711926029089277701)
  ·
    refine ⟨25147615820986130454239569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134120617711926029089277701 25147615820986130454239569)
    ·
      refine ⟨18860711865739597840679677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25147615820986130454239569 18860711865739597840679677)
      ·
        refine ⟨7072766949652349190254879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18860711865739597840679677 7072766949652349190254879)
        ·
          refine ⟨10609150424478523785382319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7072766949652349190254879 10609150424478523785382319)
          ·
            refine ⟨15913725636717785678073479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10609150424478523785382319 15913725636717785678073479)
            ·
              refine ⟨23870588455076678517110219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15913725636717785678073479 23870588455076678517110219)
              ·
                refine ⟨35805882682615017775665329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23870588455076678517110219 35805882682615017775665329)
                ·
                  refine ⟨26854412011961263331748997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35805882682615017775665329 26854412011961263331748997)
                  ·
                    refine ⟨5035202252242736874702937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26854412011961263331748997 5035202252242736874702937)
                    ·
                      refine ⟨3776401689182052656027203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5035202252242736874702937 3776401689182052656027203)
                      ·
                        rfl

theorem cell23_7354516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_7354516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354516 prefixEnd_7354516 := by exact prefixLift 7354516
  have htrace : WordTrace (prefixWord ++ tailWord_7354516) baseStart_7354516 baseEnd_7354516 := by
    simpa [prefixWord, tailWord_7354516, baseEnd_7354516] using wordTrace_append hprefix tailTrace_7354516
  have hstable : (prefixWord ++ tailWord_7354516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354516).length < 2 ^ (prefixWord ++ tailWord_7354516).sum := by decide
  have hdescent : baseEnd_7354516 < baseStart_7354516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354575 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 5]
def baseStart_7354575 : Nat := 118140960795 + 7354575 * 2 ^ 59
def prefixEnd_7354575 : Nat := 4983230072969 + 3 ^ 40 * 7354575 * 2
def baseEnd_7354575 : Nat := 3776431984540667925189431

theorem tailTrace_7354575 : CollatzResearch.WordTrace tailWord_7354575 prefixEnd_7354575 3776431984540667925189431 := by
  unfold tailWord_7354575
  simp only [CollatzResearch.WordTrace]
  refine ⟨268243387330638311254953179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178828924887092207503302119 268243387330638311254953179)
  ·
    refine ⟨402365080995957466882429769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268243387330638311254953179 402365080995957466882429769)
    ·
      refine ⟨301773810746968100161822327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402365080995957466882429769 301773810746968100161822327)
      ·
        refine ⟨452660716120452150242733491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301773810746968100161822327 452660716120452150242733491)
        ·
          refine ⟨678991074180678225364100237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452660716120452150242733491 678991074180678225364100237)
          ·
            refine ⟨254621652817754334511537589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 678991074180678225364100237 254621652817754334511537589)
            ·
              refine ⟨23870779951664468860456649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254621652817754334511537589 23870779951664468860456649)
              ·
                refine ⟨17903084963748351645342487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23870779951664468860456649 17903084963748351645342487)
                ·
                  refine ⟨26854627445622527468013731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17903084963748351645342487 26854627445622527468013731)
                  ·
                    refine ⟨40281941168433791202020597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26854627445622527468013731 40281941168433791202020597)
                    ·
                      refine ⟨3776431984540667925189431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40281941168433791202020597 3776431984540667925189431)
                      ·
                        rfl

theorem cell23_7354575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_7354575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354575 prefixEnd_7354575 := by exact prefixLift 7354575
  have htrace : WordTrace (prefixWord ++ tailWord_7354575) baseStart_7354575 baseEnd_7354575 := by
    simpa [prefixWord, tailWord_7354575, baseEnd_7354575] using wordTrace_append hprefix tailTrace_7354575
  have hstable : (prefixWord ++ tailWord_7354575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354575).length < 2 ^ (prefixWord ++ tailWord_7354575).sum := by decide
  have hdescent : baseEnd_7354575 < baseStart_7354575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354589 : List Nat := [1, 4, 3, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_7354589 : Nat := 118140960795 + 7354589 * 2 ^ 59
def prefixEnd_7354589 : Nat := 4983230072969 + 3 ^ 40 * 7354589 * 2
def baseEnd_7354589 : Nat := 3776439173269830870414367

theorem tailTrace_7354589 : CollatzResearch.WordTrace tailWord_7354589 prefixEnd_7354589 3776439173269830870414367 := by
  unfold tailWord_7354589
  simp only [CollatzResearch.WordTrace]
  refine ⟨268243897952587591645962821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178829265301725061097308547 268243897952587591645962821)
  ·
    refine ⟨50295730866110173433618029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268243897952587591645962821 50295730866110173433618029)
    ·
      refine ⟨18860899074791315037606761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50295730866110173433618029 18860899074791315037606761)
      ·
        refine ⟨14145674306093486278205071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18860899074791315037606761 14145674306093486278205071)
        ·
          refine ⟨21218511459140229417307607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14145674306093486278205071 21218511459140229417307607)
          ·
            refine ⟨31827767188710344125961411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21218511459140229417307607 31827767188710344125961411)
            ·
              refine ⟨47741650783065516188942117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31827767188710344125961411 47741650783065516188942117)
              ·
                refine ⟨8951559521824784285426647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47741650783065516188942117 8951559521824784285426647)
                ·
                  refine ⟨13427339282737176428139971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8951559521824784285426647 13427339282737176428139971)
                  ·
                    refine ⟨20141008924105764642209957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13427339282737176428139971 20141008924105764642209957)
                    ·
                      refine ⟨3776439173269830870414367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20141008924105764642209957 3776439173269830870414367)
                      ·
                        rfl

theorem cell23_7354589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_7354589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354589 prefixEnd_7354589 := by exact prefixLift 7354589
  have htrace : WordTrace (prefixWord ++ tailWord_7354589) baseStart_7354589 baseEnd_7354589 := by
    simpa [prefixWord, tailWord_7354589, baseEnd_7354589] using wordTrace_append hprefix tailTrace_7354589
  have hstable : (prefixWord ++ tailWord_7354589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354589).length < 2 ^ (prefixWord ++ tailWord_7354589).sum := by decide
  have hdescent : baseEnd_7354589 < baseStart_7354589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354623 : List Nat := [1, 1, 2, 2, 1, 4, 5, 2, 1, 2, 2]
def baseStart_7354623 : Nat := 118140960795 + 7354623 * 2 ^ 59
def prefixEnd_7354623 : Nat := 4983230072969 + 3 ^ 40 * 7354623 * 2
def baseEnd_7354623 : Nat := 3776456631612083737389211

theorem tailTrace_7354623 : CollatzResearch.WordTrace tailWord_7354623 prefixEnd_7354623 3776456631612083737389211 := by
  unfold tailWord_7354623
  simp only [CollatzResearch.WordTrace]
  refine ⟨268245138034464415452700523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178830092022976276968467015 268245138034464415452700523)
  ·
    refine ⟨402367707051696623179050785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268245138034464415452700523 402367707051696623179050785)
    ·
      refine ⟨301775780288772467384288089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402367707051696623179050785 301775780288772467384288089)
      ·
        refine ⟨226331835216579350538216067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301775780288772467384288089 226331835216579350538216067)
        ·
          refine ⟨339497752824869025807324101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226331835216579350538216067 339497752824869025807324101)
          ·
            refine ⟨63655828654662942338873269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339497752824869025807324101 63655828654662942338873269)
            ·
              refine ⟨5967733936374650844269369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63655828654662942338873269 5967733936374650844269369)
              ·
                refine ⟨4475800452280988133202027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5967733936374650844269369 4475800452280988133202027)
                ·
                  refine ⟨6713700678421482199803041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4475800452280988133202027 6713700678421482199803041)
                  ·
                    refine ⟨5035275508816111649852281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6713700678421482199803041 5035275508816111649852281)
                    ·
                      refine ⟨3776456631612083737389211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5035275508816111649852281 3776456631612083737389211)
                      ·
                        rfl

theorem cell23_7354623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 1, 2, 2].length) (baseStart_7354623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354623 prefixEnd_7354623 := by exact prefixLift 7354623
  have htrace : WordTrace (prefixWord ++ tailWord_7354623) baseStart_7354623 baseEnd_7354623 := by
    simpa [prefixWord, tailWord_7354623, baseEnd_7354623] using wordTrace_append hprefix tailTrace_7354623
  have hstable : (prefixWord ++ tailWord_7354623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354623).length < 2 ^ (prefixWord ++ tailWord_7354623).sum := by decide
  have hdescent : baseEnd_7354623 < baseStart_7354623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354625 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 2, 7]
def baseStart_7354625 : Nat := 118140960795 + 7354625 * 2 ^ 59
def prefixEnd_7354625 : Nat := 4983230072969 + 3 ^ 40 * 7354625 * 2
def baseEnd_7354625 : Nat := 1258819219524464243188067

theorem tailTrace_7354625 : CollatzResearch.WordTrace tailWord_7354625 prefixEnd_7354625 1258819219524464243188067 := by
  unfold tailWord_7354625
  simp only [CollatzResearch.WordTrace]
  refine ⟨268245210980457169794273329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178830140653638113196182219 268245210980457169794273329)
  ·
    refine ⟨201183908235342877345704997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268245210980457169794273329 201183908235342877345704997)
    ·
      refine ⟨37721982794126789502319687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201183908235342877345704997 37721982794126789502319687)
      ·
        refine ⟨56582974191190184253479531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37721982794126789502319687 56582974191190184253479531)
        ·
          refine ⟨84874461286785276380219297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56582974191190184253479531 84874461286785276380219297)
          ·
            refine ⟨63655845965088957285164473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84874461286785276380219297 63655845965088957285164473)
            ·
              refine ⟨47741884473816717963873355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63655845965088957285164473 47741884473816717963873355)
              ·
                refine ⟨71612826710725076945810033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47741884473816717963873355 71612826710725076945810033)
                ·
                  refine ⟨53709620033043807709357525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71612826710725076945810033 53709620033043807709357525)
                  ·
                    refine ⟨1258819219524464243188067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53709620033043807709357525 1258819219524464243188067)
                    ·
                      rfl

theorem cell23_7354625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_7354625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354625 prefixEnd_7354625 := by exact prefixLift 7354625
  have htrace : WordTrace (prefixWord ++ tailWord_7354625) baseStart_7354625 baseEnd_7354625 := by
    simpa [prefixWord, tailWord_7354625, baseEnd_7354625] using wordTrace_append hprefix tailTrace_7354625
  have hstable : (prefixWord ++ tailWord_7354625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354625).length < 2 ^ (prefixWord ++ tailWord_7354625).sum := by decide
  have hdescent : baseEnd_7354625 < baseStart_7354625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354679 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 4, 2, 2]
def baseStart_7354679 : Nat := 118140960795 + 7354679 * 2 ^ 59
def prefixEnd_7354679 : Nat := 4983230072969 + 3 ^ 40 * 7354679 * 2
def baseEnd_7354679 : Nat := 3776485386528735518288953

theorem tailTrace_7354679 : CollatzResearch.WordTrace tailWord_7354679 prefixEnd_7354679 3776485386528735518288953 := by
  unfold tailWord_7354679
  simp only [CollatzResearch.WordTrace]
  refine ⟨268247180522261537016739091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178831453681507691344492727 268247180522261537016739091)
  ·
    refine ⟨402370770783392305525108637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268247180522261537016739091 402370770783392305525108637)
    ·
      refine ⟨150889039043772114571915739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402370770783392305525108637 150889039043772114571915739)
      ·
        refine ⟨226333558565658171857873609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150889039043772114571915739 226333558565658171857873609)
        ·
          refine ⟨169750168924243628893405207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226333558565658171857873609 169750168924243628893405207)
          ·
            refine ⟨254625253386365443340107811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169750168924243628893405207 254625253386365443340107811)
            ·
              refine ⟨381937880079548165010161717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254625253386365443340107811 381937880079548165010161717)
              ·
                refine ⟨35806676257457640469702661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 381937880079548165010161717 35806676257457640469702661)
                ·
                  refine ⟨6713751798273307588069249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35806676257457640469702661 6713751798273307588069249)
                  ·
                    refine ⟨5035313848704980691051937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6713751798273307588069249 5035313848704980691051937)
                    ·
                      refine ⟨3776485386528735518288953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5035313848704980691051937 3776485386528735518288953)
                      ·
                        rfl

theorem cell23_7354679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 2, 2].length) (baseStart_7354679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354679 prefixEnd_7354679 := by exact prefixLift 7354679
  have htrace : WordTrace (prefixWord ++ tailWord_7354679) baseStart_7354679 baseEnd_7354679 := by
    simpa [prefixWord, tailWord_7354679, baseEnd_7354679] using wordTrace_append hprefix tailTrace_7354679
  have hstable : (prefixWord ++ tailWord_7354679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354679).length < 2 ^ (prefixWord ++ tailWord_7354679).sum := by decide
  have hdescent : baseEnd_7354679 < baseStart_7354679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354682 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3]
def baseStart_7354682 : Nat := 118140960795 + 7354682 * 2 ^ 59
def prefixEnd_7354682 : Nat := 4983230072969 + 3 ^ 40 * 7354682 * 2
def baseEnd_7354682 : Nat := 3776486926970699006551439

theorem tailTrace_7354682 : CollatzResearch.WordTrace tailWord_7354682 prefixEnd_7354682 3776486926970699006551439 := by
  unfold tailWord_7354682
  simp only [CollatzResearch.WordTrace]
  refine ⟨67061822485312667132274575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178831526627500445686065533 67061822485312667132274575)
  ·
    refine ⟨100592733727969000698411863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67061822485312667132274575 100592733727969000698411863)
    ·
      refine ⟨150889100591953501047617795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100592733727969000698411863 150889100591953501047617795)
      ·
        refine ⟨226333650887930251571426693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150889100591953501047617795 226333650887930251571426693)
        ·
          refine ⟨42437559541486922169642505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226333650887930251571426693 42437559541486922169642505)
          ·
            refine ⟨31828169656115191627231879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42437559541486922169642505 31828169656115191627231879)
            ·
              refine ⟨47742254484172787440847819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31828169656115191627231879 47742254484172787440847819)
              ·
                refine ⟨71613381726259181161271729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47742254484172787440847819 71613381726259181161271729)
                ·
                  refine ⟨53710036294694385870953797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71613381726259181161271729 53710036294694385870953797)
                  ·
                    refine ⟨10070631805255197350803837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53710036294694385870953797 10070631805255197350803837)
                    ·
                      refine ⟨3776486926970699006551439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10070631805255197350803837 3776486926970699006551439)
                      ·
                        rfl

theorem cell23_7354682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_7354682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354682 prefixEnd_7354682 := by exact prefixLift 7354682
  have htrace : WordTrace (prefixWord ++ tailWord_7354682) baseStart_7354682 baseEnd_7354682 := by
    simpa [prefixWord, tailWord_7354682, baseEnd_7354682] using wordTrace_append hprefix tailTrace_7354682
  have hstable : (prefixWord ++ tailWord_7354682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354682).length < 2 ^ (prefixWord ++ tailWord_7354682).sum := by decide
  have hdescent : baseEnd_7354682 < baseStart_7354682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354689 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 2, 6]
def baseStart_7354689 : Nat := 118140960795 + 7354689 * 2 ^ 59
def prefixEnd_7354689 : Nat := 4983230072969 + 3 ^ 40 * 7354689 * 2
def baseEnd_7354689 : Nat := 1258830173778426826387969

theorem tailTrace_7354689 : CollatzResearch.WordTrace tailWord_7354689 prefixEnd_7354689 1258830173778426826387969 := by
  unfold tailWord_7354689
  simp only [CollatzResearch.WordTrace]
  refine ⟨268247545252225308724603121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178831696834816872483068747 268247545252225308724603121)
  ·
    refine ⟨201185658939168981543452341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268247545252225308724603121 201185658939168981543452341)
    ·
      refine ⟨18861155525547092019698657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201185658939168981543452341 18861155525547092019698657)
      ·
        refine ⟨14145866644160319014773993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18861155525547092019698657 14145866644160319014773993)
        ·
          refine ⟨10609399983120239261080495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14145866644160319014773993 10609399983120239261080495)
          ·
            refine ⟨15914099974680358891620743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10609399983120239261080495 15914099974680358891620743)
            ·
              refine ⟨23871149962020538337431115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15914099974680358891620743 23871149962020538337431115)
              ·
                refine ⟨35806724943030807506146673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23871149962020538337431115 35806724943030807506146673)
                ·
                  refine ⟨26855043707273105629610005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35806724943030807506146673 26855043707273105629610005)
                  ·
                    refine ⟨1258830173778426826387969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26855043707273105629610005 1258830173778426826387969)
                    ·
                      rfl

theorem cell23_7354689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_7354689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354689 prefixEnd_7354689 := by exact prefixLift 7354689
  have htrace : WordTrace (prefixWord ++ tailWord_7354689) baseStart_7354689 baseEnd_7354689 := by
    simpa [prefixWord, tailWord_7354689, baseEnd_7354689] using wordTrace_append hprefix tailTrace_7354689
  have hstable : (prefixWord ++ tailWord_7354689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354689).length < 2 ^ (prefixWord ++ tailWord_7354689).sum := by decide
  have hdescent : baseEnd_7354689 < baseStart_7354689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354696 : List Nat := [2, 1, 3, 1, 1, 2, 4, 3, 2, 2, 2]
def baseStart_7354696 : Nat := 118140960795 + 7354696 * 2 ^ 59
def prefixEnd_7354696 : Nat := 4983230072969 + 3 ^ 40 * 7354696 * 2
def baseEnd_7354696 : Nat := 3776494115699861951776375

theorem tailTrace_7354696 : CollatzResearch.WordTrace tailWord_7354696 prefixEnd_7354696 3776494115699861951776375 := by
  unfold tailWord_7354696
  simp only [CollatzResearch.WordTrace]
  refine ⟨134123900281599974460053971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178831867042133299280071961 134123900281599974460053971)
  ·
    refine ⟨201185850422399961690080957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134123900281599974460053971 201185850422399961690080957)
    ·
      refine ⟨75444693908399985633780359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201185850422399961690080957 75444693908399985633780359)
      ·
        refine ⟨113167040862599978450670539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75444693908399985633780359 113167040862599978450670539)
        ·
          refine ⟨169750561293899967676005809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113167040862599978450670539 169750561293899967676005809)
          ·
            refine ⟨127312920970424975757004357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169750561293899967676005809 127312920970424975757004357)
            ·
              refine ⟨23871172681954682954438317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127312920970424975757004357 23871172681954682954438317)
              ·
                refine ⟨8951689755733006107914369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23871172681954682954438317 8951689755733006107914369)
                ·
                  refine ⟨6713767316799754580935777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8951689755733006107914369 6713767316799754580935777)
                  ·
                    refine ⟨5035325487599815935701833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6713767316799754580935777 5035325487599815935701833)
                    ·
                      refine ⟨3776494115699861951776375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5035325487599815935701833 3776494115699861951776375)
                      ·
                        rfl

theorem cell23_7354696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_7354696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354696 prefixEnd_7354696 := by exact prefixLift 7354696
  have htrace : WordTrace (prefixWord ++ tailWord_7354696) baseStart_7354696 baseEnd_7354696 := by
    simpa [prefixWord, tailWord_7354696, baseEnd_7354696] using wordTrace_append hprefix tailTrace_7354696
  have hstable : (prefixWord ++ tailWord_7354696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354696).length < 2 ^ (prefixWord ++ tailWord_7354696).sum := by decide
  have hdescent : baseEnd_7354696 < baseStart_7354696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354730 : List Nat := [3, 1, 3, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_7354730 : Nat := 118140960795 + 7354730 * 2 ^ 59
def prefixEnd_7354730 : Nat := 4983230072969 + 3 ^ 40 * 7354730 * 2
def baseEnd_7354730 : Nat := 3776511574042114818751219

theorem tailTrace_7354730 : CollatzResearch.WordTrace tailWord_7354730 prefixEnd_7354730 3776511574042114818751219 := by
  unfold tailWord_7354730
  simp only [CollatzResearch.WordTrace]
  refine ⟨67062260161269193181711411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178832693763384515151230429 67062260161269193181711411)
  ·
    refine ⟨100593390241903789772567117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67062260161269193181711411 100593390241903789772567117)
    ·
      refine ⟨37722521340713921164712669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100593390241903789772567117 37722521340713921164712669)
      ·
        refine ⟨14145945502767720436767251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37722521340713921164712669 14145945502767720436767251)
        ·
          refine ⟨21218918254151580655150877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14145945502767720436767251 21218918254151580655150877)
          ·
            refine ⟨7957094345306842745681579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21218918254151580655150877 7957094345306842745681579)
            ·
              refine ⟨11935641517960264118522369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7957094345306842745681579 11935641517960264118522369)
              ·
                refine ⟨8951731138470198088891777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11935641517960264118522369 8951731138470198088891777)
                ·
                  refine ⟨6713798353852648566668833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8951731138470198088891777 6713798353852648566668833)
                  ·
                    refine ⟨5035348765389486425001625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6713798353852648566668833 5035348765389486425001625)
                    ·
                      refine ⟨3776511574042114818751219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5035348765389486425001625 3776511574042114818751219)
                      ·
                        rfl

theorem cell23_7354730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_7354730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354730 prefixEnd_7354730 := by exact prefixLift 7354730
  have htrace : WordTrace (prefixWord ++ tailWord_7354730) baseStart_7354730 baseEnd_7354730 := by
    simpa [prefixWord, tailWord_7354730, baseEnd_7354730] using wordTrace_append hprefix tailTrace_7354730
  have hstable : (prefixWord ++ tailWord_7354730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354730).length < 2 ^ (prefixWord ++ tailWord_7354730).sum := by decide
  have hdescent : baseEnd_7354730 < baseStart_7354730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354789 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 2, 2, 3]
def baseStart_7354789 : Nat := 118140960795 + 7354789 * 2 ^ 59
def prefixEnd_7354789 : Nat := 4983230072969 + 3 ^ 40 * 7354789 * 2
def baseEnd_7354789 : Nat := 3776541869400730087913447

theorem tailTrace_7354789 : CollatzResearch.WordTrace tailWord_7354789 prefixEnd_7354789 3776541869400730087913447 := by
  unfold tailWord_7354789
  simp only [CollatzResearch.WordTrace]
  refine ⟨268251192551863025803243421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178834128367908683868828947 268251192551863025803243421)
  ·
    refine ⟨100594197206948634676216283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268251192551863025803243421 100594197206948634676216283)
    ·
      refine ⟨150891295810422952014324425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100594197206948634676216283 150891295810422952014324425)
      ·
        refine ⟨113168471857817214010743319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150891295810422952014324425 113168471857817214010743319)
        ·
          refine ⟨169752707786725821016114979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113168471857817214010743319 169752707786725821016114979)
          ·
            refine ⟨254629061680088731524172469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169752707786725821016114979 254629061680088731524172469)
            ·
              refine ⟨23871474532508318580391169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254629061680088731524172469 23871474532508318580391169)
              ·
                refine ⟨17903605899381238935293377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23871474532508318580391169 17903605899381238935293377)
                ·
                  refine ⟨13427704424535929201470033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17903605899381238935293377 13427704424535929201470033)
                  ·
                    refine ⟨10070778318401946901102525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13427704424535929201470033 10070778318401946901102525)
                    ·
                      refine ⟨3776541869400730087913447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10070778318401946901102525 3776541869400730087913447)
                      ·
                        rfl

theorem cell23_7354789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_7354789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354789 prefixEnd_7354789 := by exact prefixLift 7354789
  have htrace : WordTrace (prefixWord ++ tailWord_7354789) baseStart_7354789 baseEnd_7354789 := by
    simpa [prefixWord, tailWord_7354789, baseEnd_7354789] using wordTrace_append hprefix tailTrace_7354789
  have hstable : (prefixWord ++ tailWord_7354789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354789).length < 2 ^ (prefixWord ++ tailWord_7354789).sum := by decide
  have hdescent : baseEnd_7354789 < baseStart_7354789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354809 : List Nat := [1, 2, 1, 4, 3, 2, 1, 3, 6]
def baseStart_7354809 : Nat := 118140960795 + 7354809 * 2 ^ 59
def prefixEnd_7354809 : Nat := 4983230072969 + 3 ^ 40 * 7354809 * 2
def baseEnd_7354809 : Nat := 419616904334868889962595

theorem tailTrace_7354809 : CollatzResearch.WordTrace tailWord_7354809 prefixEnd_7354809 419616904334868889962595 := by
  unfold tailWord_7354809
  simp only [CollatzResearch.WordTrace]
  refine ⟨268251922011790569218971481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178834614674527046145980987 268251922011790569218971481)
  ·
    refine ⟨201188941508842926914228611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268251922011790569218971481 201188941508842926914228611)
    ·
      refine ⟨301783412263264390371342917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201188941508842926914228611 301783412263264390371342917)
      ·
        refine ⟨56584389799362073194626797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301783412263264390371342917 56584389799362073194626797)
        ·
          refine ⟨21219146174760777447985049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56584389799362073194626797 21219146174760777447985049)
          ·
            refine ⟨15914359631070583085988787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21219146174760777447985049 15914359631070583085988787)
            ·
              refine ⟨23871539446605874628983181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15914359631070583085988787 23871539446605874628983181)
              ·
                refine ⟨8951827292477202985868693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23871539446605874628983181 8951827292477202985868693)
                ·
                  refine ⟨419616904334868889962595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8951827292477202985868693 419616904334868889962595)
                  ·
                    rfl

theorem cell23_7354809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 6].length) (baseStart_7354809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354809 prefixEnd_7354809 := by exact prefixLift 7354809
  have htrace : WordTrace (prefixWord ++ tailWord_7354809) baseStart_7354809 baseEnd_7354809 := by
    simpa [prefixWord, tailWord_7354809, baseEnd_7354809] using wordTrace_append hprefix tailTrace_7354809
  have hstable : (prefixWord ++ tailWord_7354809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354809).length < 2 ^ (prefixWord ++ tailWord_7354809).sum := by decide
  have hdescent : baseEnd_7354809 < baseStart_7354809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354819 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 5, 1, 3]
def baseStart_7354819 : Nat := 118140960795 + 7354819 * 2 ^ 59
def prefixEnd_7354819 : Nat := 4983230072969 + 3 ^ 40 * 7354819 * 2
def baseEnd_7354819 : Nat := 3776557273820364970538309

theorem tailTrace_7354819 : CollatzResearch.WordTrace tailWord_7354819 prefixEnd_7354819 3776557273820364970538309 := by
  unfold tailWord_7354819
  simp only [CollatzResearch.WordTrace]
  refine ⟨268252286741754340926835511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178834857827836227284557007 268252286741754340926835511)
  ·
    refine ⟨402378430112631511390253267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268252286741754340926835511 402378430112631511390253267)
    ·
      refine ⟨603567645168947267085379901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402378430112631511390253267 603567645168947267085379901)
      ·
        refine ⟨226337866938355225157017463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 603567645168947267085379901 226337866938355225157017463)
        ·
          refine ⟨339506800407532837735526195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226337866938355225157017463 339506800407532837735526195)
          ·
            refine ⟨509260200611299256603289293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339506800407532837735526195 509260200611299256603289293)
            ·
              refine ⟨190972575229237221226233485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 509260200611299256603289293 190972575229237221226233485)
              ·
                refine ⟨71614715710963957959837557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190972575229237221226233485 71614715710963957959837557)
                ·
                  refine ⟨6713879597902871058734771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71614715710963957959837557 6713879597902871058734771)
                  ·
                    refine ⟨10070819396854306588102157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6713879597902871058734771 10070819396854306588102157)
                    ·
                      refine ⟨3776557273820364970538309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10070819396854306588102157 3776557273820364970538309)
                      ·
                        rfl

theorem cell23_7354819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_7354819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354819 prefixEnd_7354819 := by exact prefixLift 7354819
  have htrace : WordTrace (prefixWord ++ tailWord_7354819) baseStart_7354819 baseEnd_7354819 := by
    simpa [prefixWord, tailWord_7354819, baseEnd_7354819] using wordTrace_append hprefix tailTrace_7354819
  have hstable : (prefixWord ++ tailWord_7354819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354819).length < 2 ^ (prefixWord ++ tailWord_7354819).sum := by decide
  have hdescent : baseEnd_7354819 < baseStart_7354819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354879 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 3]
def baseStart_7354879 : Nat := 118140960795 + 7354879 * 2 ^ 59
def prefixEnd_7354879 : Nat := 4983230072969 + 3 ^ 40 * 7354879 * 2
def baseEnd_7354879 : Nat := 3776588082659634735788033

theorem tailTrace_7354879 : CollatzResearch.WordTrace tailWord_7354879 prefixEnd_7354879 3776588082659634735788033 := by
  unfold tailWord_7354879
  simp only [CollatzResearch.WordTrace]
  refine ⟨268254475121536971174019691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178836316747691314116013127 268254475121536971174019691)
  ·
    refine ⟨402381712682305456761029537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268254475121536971174019691 402381712682305456761029537)
    ·
      refine ⟨301786284511729092570772153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402381712682305456761029537 301786284511729092570772153)
      ·
        refine ⟨226339713383796819428079115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301786284511729092570772153 226339713383796819428079115)
        ·
          refine ⟨339509570075695229142118673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226339713383796819428079115 339509570075695229142118673)
          ·
            refine ⟨254632177556771421856589005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339509570075695229142118673 254632177556771421856589005)
            ·
              refine ⟨95487066583789283196220877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254632177556771421856589005 95487066583789283196220877)
              ·
                refine ⟨35807649968920981198582829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95487066583789283196220877 35807649968920981198582829)
                ·
                  refine ⟨13427868738345367949468561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35807649968920981198582829 13427868738345367949468561)
                  ·
                    refine ⟨10070901553759025962101421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13427868738345367949468561 10070901553759025962101421)
                    ·
                      refine ⟨3776588082659634735788033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10070901553759025962101421 3776588082659634735788033)
                      ·
                        rfl

theorem cell23_7354879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_7354879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354879 prefixEnd_7354879 := by exact prefixLift 7354879
  have htrace : WordTrace (prefixWord ++ tailWord_7354879) baseStart_7354879 baseEnd_7354879 := by
    simpa [prefixWord, tailWord_7354879, baseEnd_7354879] using wordTrace_append hprefix tailTrace_7354879
  have hstable : (prefixWord ++ tailWord_7354879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354879).length < 2 ^ (prefixWord ++ tailWord_7354879).sum := by decide
  have hdescent : baseEnd_7354879 < baseStart_7354879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354903 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 4, 4]
def baseStart_7354903 : Nat := 118140960795 + 7354903 * 2 ^ 59
def prefixEnd_7354903 : Nat := 4983230072969 + 3 ^ 40 * 7354903 * 2
def baseEnd_7354903 : Nat := 1258866802065114213962641

theorem tailTrace_7354903 : CollatzResearch.WordTrace tailWord_7354903 prefixEnd_7354903 1258866802065114213962641 := by
  unfold tailWord_7354903
  simp only [CollatzResearch.WordTrace]
  refine ⟨268255350473450023272893363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178836900315633348848595575 268255350473450023272893363)
  ·
    refine ⟨402383025710175034909340045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268255350473450023272893363 402383025710175034909340045)
    ·
      refine ⟨150893634641315638091002517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402383025710175034909340045 150893634641315638091002517)
      ·
        refine ⟨7073139123811670535515743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150893634641315638091002517 7073139123811670535515743)
        ·
          refine ⟨10609708685717505803273615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7073139123811670535515743 10609708685717505803273615)
          ·
            refine ⟨15914563028576258704910423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10609708685717505803273615 15914563028576258704910423)
            ·
              refine ⟨23871844542864388057365635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15914563028576258704910423 23871844542864388057365635)
              ·
                refine ⟨35807766814296582086048453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23871844542864388057365635 35807766814296582086048453)
                ·
                  refine ⟨6713956277680609141134085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35807766814296582086048453 6713956277680609141134085)
                  ·
                    refine ⟨1258866802065114213962641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6713956277680609141134085 1258866802065114213962641)
                    ·
                      rfl

theorem cell23_7354903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_7354903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354903 prefixEnd_7354903 := by exact prefixLift 7354903
  have htrace : WordTrace (prefixWord ++ tailWord_7354903) baseStart_7354903 baseEnd_7354903 := by
    simpa [prefixWord, tailWord_7354903, baseEnd_7354903] using wordTrace_append hprefix tailTrace_7354903
  have hstable : (prefixWord ++ tailWord_7354903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354903).length < 2 ^ (prefixWord ++ tailWord_7354903).sum := by decide
  have hdescent : baseEnd_7354903 < baseStart_7354903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354920 : List Nat := [2, 1, 5, 2, 1, 2, 3, 1, 2, 4]
def baseStart_7354920 : Nat := 118140960795 + 7354920 * 2 ^ 59
def prefixEnd_7354920 : Nat := 4983230072969 + 3 ^ 40 * 7354920 * 2
def baseEnd_7354920 : Nat := 1258869711788823025125115

theorem tailTrace_7354920 : CollatzResearch.WordTrace tailWord_7354920 prefixEnd_7354920 1258869711788823025125115 := by
  unfold tailWord_7354920
  simp only [CollatzResearch.WordTrace]
  refine ⟨134127985257194217588131107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178837313676258956784174809 134127985257194217588131107)
  ·
    refine ⟨201191977885791326382196661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134127985257194217588131107 201191977885791326382196661)
    ·
      refine ⟨18861747926792936848330937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201191977885791326382196661 18861747926792936848330937)
      ·
        refine ⟨14146310945094702636248203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18861747926792936848330937 14146310945094702636248203)
        ·
          refine ⟨21219466417642053954372305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14146310945094702636248203 21219466417642053954372305)
          ·
            refine ⟨15914599813231540465779229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21219466417642053954372305 15914599813231540465779229)
            ·
              refine ⟨5967974929961827674667211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15914599813231540465779229 5967974929961827674667211)
              ·
                refine ⟨8951962394942741512000817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5967974929961827674667211 8951962394942741512000817)
                ·
                  refine ⟨6713971796207056134000613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8951962394942741512000817 6713971796207056134000613)
                  ·
                    refine ⟨1258869711788823025125115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6713971796207056134000613 1258869711788823025125115)
                    ·
                      rfl

theorem cell23_7354920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_7354920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354920 prefixEnd_7354920 := by exact prefixLift 7354920
  have htrace : WordTrace (prefixWord ++ tailWord_7354920) baseStart_7354920 baseEnd_7354920 := by
    simpa [prefixWord, tailWord_7354920, baseEnd_7354920] using wordTrace_append hprefix tailTrace_7354920
  have hstable : (prefixWord ++ tailWord_7354920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354920).length < 2 ^ (prefixWord ++ tailWord_7354920).sum := by decide
  have hdescent : baseEnd_7354920 < baseStart_7354920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7354979 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 4]
def baseStart_7354979 : Nat := 118140960795 + 7354979 * 2 ^ 59
def prefixEnd_7354979 : Nat := 4983230072969 + 3 ^ 40 * 7354979 * 2
def baseEnd_7354979 : Nat := 3776639430725084344537573

theorem tailTrace_7354979 : CollatzResearch.WordTrace tailWord_7354979 prefixEnd_7354979 3776639430725084344537573 := by
  unfold tailWord_7354979
  simp only [CollatzResearch.WordTrace]
  refine ⟨268258122421174688252659991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178838748280783125501773327 268258122421174688252659991)
  ·
    refine ⟨402387183631762032378989987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268258122421174688252659991 402387183631762032378989987)
    ·
      refine ⟨603580775447643048568484981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402387183631762032378989987 603580775447643048568484981)
      ·
        refine ⟨56585697698216535803295467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 603580775447643048568484981 56585697698216535803295467)
        ·
          refine ⟨84878546547324803704943201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56585697698216535803295467 84878546547324803704943201)
          ·
            refine ⟨63658909910493602778707401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84878546547324803704943201 63658909910493602778707401)
            ·
              refine ⟨47744182432870202084030551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63658909910493602778707401 47744182432870202084030551)
              ·
                refine ⟨71616273649305303126045827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47744182432870202084030551 71616273649305303126045827)
                ·
                  refine ⟨107424410473957954689068741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71616273649305303126045827 107424410473957954689068741)
                  ·
                    refine ⟨20142076963867116504200389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107424410473957954689068741 20142076963867116504200389)
                    ·
                      refine ⟨3776639430725084344537573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20142076963867116504200389 3776639430725084344537573)
                      ·
                        rfl

theorem cell23_7354979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_7354979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7354979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7354979 prefixEnd_7354979 := by exact prefixLift 7354979
  have htrace : WordTrace (prefixWord ++ tailWord_7354979) baseStart_7354979 baseEnd_7354979 := by
    simpa [prefixWord, tailWord_7354979, baseEnd_7354979] using wordTrace_append hprefix tailTrace_7354979
  have hstable : (prefixWord ++ tailWord_7354979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7354979).length < 2 ^ (prefixWord ++ tailWord_7354979).sum := by decide
  have hdescent : baseEnd_7354979 < baseStart_7354979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7354979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355019 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 4, 5]
def baseStart_7355019 : Nat := 118140960795 + 7355019 * 2 ^ 59
def prefixEnd_7355019 : Nat := 4983230072969 + 3 ^ 40 * 7355019 * 2
def baseEnd_7355019 : Nat := 1258886656650421396012463

theorem tailTrace_7355019 : CollatzResearch.WordTrace tailWord_7355019 prefixEnd_7355019 1258886656650421396012463 := by
  unfold tailWord_7355019
  simp only [CollatzResearch.WordTrace]
  refine ⟨268259581341029775084116111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178839720894019850056077407 268259581341029775084116111)
  ·
    refine ⟨402389372011544662626174167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268259581341029775084116111 402389372011544662626174167)
    ·
      refine ⟨603584058017316993939261251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402389372011544662626174167 603584058017316993939261251)
      ·
        refine ⟨905376087025975490908891877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603584058017316993939261251 905376087025975490908891877)
        ·
          refine ⟨169758016317370404545417227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 905376087025975490908891877 169758016317370404545417227)
          ·
            refine ⟨254637024476055606818125841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169758016317370404545417227 254637024476055606818125841)
            ·
              refine ⟨190977768357041705113594381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254637024476055606818125841 190977768357041705113594381)
              ·
                refine ⟨71616663133890639417597893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190977768357041705113594381 71616663133890639417597893)
                ·
                  refine ⟨13428124337604494890799605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71616663133890639417597893 13428124337604494890799605)
                  ·
                    refine ⟨1258886656650421396012463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13428124337604494890799605 1258886656650421396012463)
                    ·
                      rfl

theorem cell23_7355019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 5].length) (baseStart_7355019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355019 prefixEnd_7355019 := by exact prefixLift 7355019
  have htrace : WordTrace (prefixWord ++ tailWord_7355019) baseStart_7355019 baseEnd_7355019 := by
    simpa [prefixWord, tailWord_7355019, baseEnd_7355019] using wordTrace_append hprefix tailTrace_7355019
  have hstable : (prefixWord ++ tailWord_7355019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355019).length < 2 ^ (prefixWord ++ tailWord_7355019).sum := by decide
  have hdescent : baseEnd_7355019 < baseStart_7355019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355053 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_7355053 : Nat := 118140960795 + 7355053 * 2 ^ 59
def prefixEnd_7355053 : Nat := 4983230072969 + 3 ^ 40 * 7355053 * 2
def baseEnd_7355053 : Nat := 1258892476097839018337411

theorem tailTrace_7355053 : CollatzResearch.WordTrace tailWord_7355053 prefixEnd_7355053 1258892476097839018337411 := by
  unfold tailWord_7355053
  simp only [CollatzResearch.WordTrace]
  refine ⟨268260821422906598890853813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178840547615271065927235875 268260821422906598890853813)
  ·
    refine ⟨25149452008397493646017545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268260821422906598890853813 25149452008397493646017545)
    ·
      refine ⟨18862089006298120234513159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25149452008397493646017545 18862089006298120234513159)
      ·
        refine ⟨28293133509447180351769739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18862089006298120234513159 28293133509447180351769739)
        ·
          refine ⟨42439700264170770527654609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28293133509447180351769739 42439700264170770527654609)
          ·
            refine ⟨31829775198128077895740957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42439700264170770527654609 31829775198128077895740957)
            ·
              refine ⟨11936165699298029210902859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31829775198128077895740957 11936165699298029210902859)
              ·
                refine ⟨17904248548947043816354289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11936165699298029210902859 17904248548947043816354289)
                ·
                  refine ⟨13428186411710282862265717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17904248548947043816354289 13428186411710282862265717)
                  ·
                    refine ⟨1258892476097839018337411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13428186411710282862265717 1258892476097839018337411)
                    ·
                      rfl

theorem cell23_7355053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_7355053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355053 prefixEnd_7355053 := by exact prefixLift 7355053
  have htrace : WordTrace (prefixWord ++ tailWord_7355053) baseStart_7355053 baseEnd_7355053 := by
    simpa [prefixWord, tailWord_7355053, baseEnd_7355053] using wordTrace_append hprefix tailTrace_7355053
  have hstable : (prefixWord ++ tailWord_7355053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355053).length < 2 ^ (prefixWord ++ tailWord_7355053).sum := by decide
  have hdescent : baseEnd_7355053 < baseStart_7355053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355056 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 3, 6, 2]
def baseStart_7355056 : Nat := 118140960795 + 7355056 * 2 ^ 59
def prefixEnd_7355056 : Nat := 4983230072969 + 3 ^ 40 * 7355056 * 2
def baseEnd_7355056 : Nat := 3776678968735480543274719

theorem tailTrace_7355056 : CollatzResearch.WordTrace tailWord_7355056 prefixEnd_7355056 3776678968735480543274719 := by
  unfold tailWord_7355056
  simp only [CollatzResearch.WordTrace]
  refine ⟨134130465420947865201606511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178840620561263820268808681 134130465420947865201606511)
  ·
    refine ⟨201195698131421797802409767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134130465420947865201606511 201195698131421797802409767)
    ·
      refine ⟨301793547197132696703614651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201195698131421797802409767 301793547197132696703614651)
      ·
        refine ⟨452690320795699045055421977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301793547197132696703614651 452690320795699045055421977)
        ·
          refine ⟨339517740596774283791566483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452690320795699045055421977 339517740596774283791566483)
          ·
            refine ⟨509276610895161425687349725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339517740596774283791566483 509276610895161425687349725)
            ·
              refine ⟨190978729085685534632756147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 509276610895161425687349725 190978729085685534632756147)
              ·
                refine ⟨286468093628528301949134221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190978729085685534632756147 286468093628528301949134221)
                ·
                  refine ⟨107425535110698113230925333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286468093628528301949134221 107425535110698113230925333)
                  ·
                    refine ⟨5035571958313974057699625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107425535110698113230925333 5035571958313974057699625)
                    ·
                      refine ⟨3776678968735480543274719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5035571958313974057699625 3776678968735480543274719)
                      ·
                        rfl

theorem cell23_7355056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 6, 2].length) (baseStart_7355056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355056 prefixEnd_7355056 := by exact prefixLift 7355056
  have htrace : WordTrace (prefixWord ++ tailWord_7355056) baseStart_7355056 baseEnd_7355056 := by
    simpa [prefixWord, tailWord_7355056, baseEnd_7355056] using wordTrace_append hprefix tailTrace_7355056
  have hstable : (prefixWord ++ tailWord_7355056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355056).length < 2 ^ (prefixWord ++ tailWord_7355056).sum := by decide
  have hdescent : baseEnd_7355056 < baseStart_7355056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355066 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 5, 4]
def baseStart_7355066 : Nat := 118140960795 + 7355066 * 2 ^ 59
def prefixEnd_7355066 : Nat := 4983230072969 + 3 ^ 40 * 7355066 * 2
def baseEnd_7355066 : Nat := 1258894701180675168049891

theorem tailTrace_7355066 : CollatzResearch.WordTrace tailWord_7355066 prefixEnd_7355066 1258894701180675168049891 := by
  unfold tailWord_7355066
  simp only [CollatzResearch.WordTrace]
  refine ⟨67065323892964875527769263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178840863714573001407384701 67065323892964875527769263)
  ·
    refine ⟨100597985839447313291653895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67065323892964875527769263 100597985839447313291653895)
    ·
      refine ⟨150896978759170969937480843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100597985839447313291653895 150896978759170969937480843)
      ·
        refine ⟨226345468138756454906221265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150896978759170969937480843 226345468138756454906221265)
        ·
          refine ⟨169759101104067341179665949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226345468138756454906221265 169759101104067341179665949)
          ·
            refine ⟨63659662914025252942374731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169759101104067341179665949 63659662914025252942374731)
            ·
              refine ⟨95489494371037879413562097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63659662914025252942374731 95489494371037879413562097)
              ·
                refine ⟨71617120778278409560171573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95489494371037879413562097 71617120778278409560171573)
                ·
                  refine ⟨6714105072963600896266085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71617120778278409560171573 6714105072963600896266085)
                  ·
                    refine ⟨1258894701180675168049891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6714105072963600896266085 1258894701180675168049891)
                    ·
                      rfl

theorem cell23_7355066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_7355066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355066 prefixEnd_7355066 := by exact prefixLift 7355066
  have htrace : WordTrace (prefixWord ++ tailWord_7355066) baseStart_7355066 baseEnd_7355066 := by
    simpa [prefixWord, tailWord_7355066, baseEnd_7355066] using wordTrace_append hprefix tailTrace_7355066
  have hstable : (prefixWord ++ tailWord_7355066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355066).length < 2 ^ (prefixWord ++ tailWord_7355066).sum := by decide
  have hdescent : baseEnd_7355066 < baseStart_7355066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355100 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 3, 4]
def baseStart_7355100 : Nat := 118140960795 + 7355100 * 2 ^ 59
def prefixEnd_7355100 : Nat := 4983230072969 + 3 ^ 40 * 7355100 * 2
def baseEnd_7355100 : Nat := 1258900520628092790374839

theorem tailTrace_7355100 : CollatzResearch.WordTrace tailWord_7355100 prefixEnd_7355100 1258900520628092790374839 := by
  unfold tailWord_7355100
  simp only [CollatzResearch.WordTrace]
  refine ⟨134131267826868162958907377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178841690435824217278543169 134131267826868162958907377)
  ·
    refine ⟨100598450870151122219180533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134131267826868162958907377 100598450870151122219180533)
    ·
      refine ⟨9431104769076667708048175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100598450870151122219180533 9431104769076667708048175)
      ·
        refine ⟨14146657153615001562072263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9431104769076667708048175 14146657153615001562072263)
        ·
          refine ⟨21219985730422502343108395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14146657153615001562072263 21219985730422502343108395)
          ·
            refine ⟨31829978595633753514662593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21219985730422502343108395 31829978595633753514662593)
            ·
              refine ⟨23872483946725315135996945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31829978595633753514662593 23872483946725315135996945)
              ·
                refine ⟨17904362960043986351997709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23872483946725315135996945 17904362960043986351997709)
                ·
                  refine ⟨6714136110016494881999141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17904362960043986351997709 6714136110016494881999141)
                  ·
                    refine ⟨1258900520628092790374839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6714136110016494881999141 1258900520628092790374839)
                    ·
                      rfl

theorem cell23_7355100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_7355100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355100 prefixEnd_7355100 := by exact prefixLift 7355100
  have htrace : WordTrace (prefixWord ++ tailWord_7355100) baseStart_7355100 baseEnd_7355100 := by
    simpa [prefixWord, tailWord_7355100, baseEnd_7355100] using wordTrace_append hprefix tailTrace_7355100
  have hstable : (prefixWord ++ tailWord_7355100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355100).length < 2 ^ (prefixWord ++ tailWord_7355100).sum := by decide
  have hdescent : baseEnd_7355100 < baseStart_7355100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355134 : List Nat := [4, 2, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_7355134 : Nat := 118140960795 + 7355134 * 2 ^ 59
def prefixEnd_7355134 : Nat := 4983230072969 + 3 ^ 40 * 7355134 * 2
def baseEnd_7355134 : Nat := 1258906340075510412699787

theorem tailTrace_7355134 : CollatzResearch.WordTrace tailWord_7355134 prefixEnd_7355134 1258906340075510412699787 := by
  unfold tailWord_7355134
  simp only [CollatzResearch.WordTrace]
  refine ⟨33532971966951643715569057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178842517157075433149701637 33532971966951643715569057)
  ·
    refine ⟨25149728975213732786676793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33532971966951643715569057 25149728975213732786676793)
    ·
      refine ⟨18862296731410299590007595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25149728975213732786676793 18862296731410299590007595)
      ·
        refine ⟨28293445097115449385011393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18862296731410299590007595 28293445097115449385011393)
        ·
          refine ⟨21220083822836587038758545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28293445097115449385011393 21220083822836587038758545)
          ·
            refine ⟨15915062867127440279068909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21220083822836587038758545 15915062867127440279068909)
            ·
              refine ⟨5968148575172790104650841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15915062867127440279068909 5968148575172790104650841)
              ·
                refine ⟨4476111431379592578488131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5968148575172790104650841 4476111431379592578488131)
                ·
                  refine ⟨6714167147069388867732197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476111431379592578488131 6714167147069388867732197)
                  ·
                    refine ⟨1258906340075510412699787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6714167147069388867732197 1258906340075510412699787)
                    ·
                      rfl

theorem cell23_7355134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_7355134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355134 prefixEnd_7355134 := by exact prefixLift 7355134
  have htrace : WordTrace (prefixWord ++ tailWord_7355134) baseStart_7355134 baseEnd_7355134 := by
    simpa [prefixWord, tailWord_7355134, baseEnd_7355134] using wordTrace_append hprefix tailTrace_7355134
  have hstable : (prefixWord ++ tailWord_7355134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355134).length < 2 ^ (prefixWord ++ tailWord_7355134).sum := by decide
  have hdescent : baseEnd_7355134 < baseStart_7355134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355180 : List Nat := [2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 4]
def baseStart_7355180 : Nat := 118140960795 + 7355180 * 2 ^ 59
def prefixEnd_7355180 : Nat := 4983230072969 + 3 ^ 40 * 7355180 * 2
def baseEnd_7355180 : Nat := 3776742640336638058124149

theorem tailTrace_7355180 : CollatzResearch.WordTrace tailWord_7355180 prefixEnd_7355180 3776742640336638058124149 := by
  unfold tailWord_7355180
  simp only [CollatzResearch.WordTrace]
  refine ⟨134132726746723249790363497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178843635662297666387151329 134132726746723249790363497)
  ·
    refine ⟨100599545060042437342772623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134132726746723249790363497 100599545060042437342772623)
    ·
      refine ⟨150899317590063656014158935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100599545060042437342772623 150899317590063656014158935)
      ·
        refine ⟨226348976385095484021238403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150899317590063656014158935 226348976385095484021238403)
        ·
          refine ⟨339523464577643226031857605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226348976385095484021238403 339523464577643226031857605)
          ·
            refine ⟨63660649608308104880973301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339523464577643226031857605 63660649608308104880973301)
            ·
              refine ⟨5968185900778884832591247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63660649608308104880973301 5968185900778884832591247)
              ·
                refine ⟨8952278851168327248886871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5968185900778884832591247 8952278851168327248886871)
                ·
                  refine ⟨13428418276752490873330307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8952278851168327248886871 13428418276752490873330307)
                  ·
                    refine ⟨20142627415128736309995461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13428418276752490873330307 20142627415128736309995461)
                    ·
                      refine ⟨3776742640336638058124149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20142627415128736309995461 3776742640336638058124149)
                      ·
                        rfl

theorem cell23_7355180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 4].length) (baseStart_7355180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355180 prefixEnd_7355180 := by exact prefixLift 7355180
  have htrace : WordTrace (prefixWord ++ tailWord_7355180) baseStart_7355180 baseEnd_7355180 := by
    simpa [prefixWord, tailWord_7355180, baseEnd_7355180] using wordTrace_append hprefix tailTrace_7355180
  have hstable : (prefixWord ++ tailWord_7355180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355180).length < 2 ^ (prefixWord ++ tailWord_7355180).sum := by decide
  have hdescent : baseEnd_7355180 < baseStart_7355180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355220 : List Nat := [2, 4, 1, 1, 4, 1, 3, 7]
def baseStart_7355220 : Nat := 118140960795 + 7355220 * 2 ^ 59
def prefixEnd_7355220 : Nat := 4983230072969 + 3 ^ 40 * 7355220 * 2
def baseEnd_7355220 : Nat := 139880117761585848208295

theorem tailTrace_7355220 : CollatzResearch.WordTrace tailWord_7355220 prefixEnd_7355220 139880117761585848208295 := by
  unfold tailWord_7355220
  simp only [CollatzResearch.WordTrace]
  refine ⟨134133456206650793206091557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178844608275534390941455409 134133456206650793206091557)
  ·
    refine ⟨25150023038747023726142167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134133456206650793206091557 25150023038747023726142167)
    ·
      refine ⟨37725034558120535589213251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25150023038747023726142167 37725034558120535589213251)
      ·
        refine ⟨56587551837180803383819877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37725034558120535589213251 56587551837180803383819877)
        ·
          refine ⟨10610165969471400634466227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56587551837180803383819877 10610165969471400634466227)
          ·
            refine ⟨15915248954207100951699341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10610165969471400634466227 15915248954207100951699341)
            ·
              refine ⟨5968218357827662856887253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15915248954207100951699341 5968218357827662856887253)
              ·
                refine ⟨139880117761585848208295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5968218357827662856887253 139880117761585848208295)
                ·
                  rfl

theorem cell23_7355220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 7].length) (baseStart_7355220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355220 prefixEnd_7355220 := by exact prefixLift 7355220
  have htrace : WordTrace (prefixWord ++ tailWord_7355220) baseStart_7355220 baseEnd_7355220 := by
    simpa [prefixWord, tailWord_7355220, baseEnd_7355220] using wordTrace_append hprefix tailTrace_7355220
  have hstable : (prefixWord ++ tailWord_7355220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355220).length < 2 ^ (prefixWord ++ tailWord_7355220).sum := by decide
  have hdescent : baseEnd_7355220 < baseStart_7355220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355256 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_7355256 : Nat := 118140960795 + 7355256 * 2 ^ 59
def prefixEnd_7355256 : Nat := 4983230072969 + 3 ^ 40 * 7355256 * 2
def baseEnd_7355256 : Nat := 3776781664866379760773799

theorem tailTrace_7355256 : CollatzResearch.WordTrace tailWord_7355256 prefixEnd_7355256 3776781664866379760773799 := by
  unfold tailWord_7355256
  simp only [CollatzResearch.WordTrace]
  refine ⟨134134112720585582280246811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178845483627447443040329081 134134112720585582280246811)
  ·
    refine ⟨201201169080878373420370217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134134112720585582280246811 201201169080878373420370217)
    ·
      refine ⟨150900876810658780065277663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201201169080878373420370217 150900876810658780065277663)
      ·
        refine ⟨226351315215988170097916495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150900876810658780065277663 226351315215988170097916495)
        ·
          refine ⟨339526972823982255146874743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226351315215988170097916495 339526972823982255146874743)
          ·
            refine ⟨509290459235973382720312115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339526972823982255146874743 509290459235973382720312115)
            ·
              refine ⟨763935688853960074080468173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509290459235973382720312115 763935688853960074080468173)
              ·
                refine ⟨286475883320235027780175565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 763935688853960074080468173 286475883320235027780175565)
                ·
                  refine ⟨107428456245088135417565837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286475883320235027780175565 107428456245088135417565837)
                  ·
                    refine ⟨40285671091908050781587189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107428456245088135417565837 40285671091908050781587189)
                    ·
                      refine ⟨3776781664866379760773799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40285671091908050781587189 3776781664866379760773799)
                      ·
                        rfl

theorem cell23_7355256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_7355256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355256 prefixEnd_7355256 := by exact prefixLift 7355256
  have htrace : WordTrace (prefixWord ++ tailWord_7355256) baseStart_7355256 baseEnd_7355256 := by
    simpa [prefixWord, tailWord_7355256, baseEnd_7355256] using wordTrace_append hprefix tailTrace_7355256
  have hstable : (prefixWord ++ tailWord_7355256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355256).length < 2 ^ (prefixWord ++ tailWord_7355256).sum := by decide
  have hdescent : baseEnd_7355256 < baseStart_7355256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355274 : List Nat := [3, 1, 2, 4, 1, 2, 2, 2, 1, 3, 2]
def baseStart_7355274 : Nat := 118140960795 + 7355274 * 2 ^ 59
def prefixEnd_7355274 : Nat := 4983230072969 + 3 ^ 40 * 7355274 * 2
def baseEnd_7355274 : Nat := 3776790907518160690348717

theorem tailTrace_7355274 : CollatzResearch.WordTrace tailWord_7355274 prefixEnd_7355274 3776790907518160690348717 := by
  unfold tailWord_7355274
  simp only [CollatzResearch.WordTrace]
  refine ⟨67067220488776488408662219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178845921303403969089765917 67067220488776488408662219)
  ·
    refine ⟨100600830733164732612993329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67067220488776488408662219 100600830733164732612993329)
    ·
      refine ⟨75450623049873549459744997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100600830733164732612993329 75450623049873549459744997)
      ·
        refine ⟨14146991821851290523702187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75450623049873549459744997 14146991821851290523702187)
        ·
          refine ⟨21220487732776935785553281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14146991821851290523702187 21220487732776935785553281)
          ·
            refine ⟨15915365799582701839164961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21220487732776935785553281 15915365799582701839164961)
            ·
              refine ⟨11936524349687026379373721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15915365799582701839164961 11936524349687026379373721)
              ·
                refine ⟨8952393262265269784530291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11936524349687026379373721 8952393262265269784530291)
                ·
                  refine ⟨13428589893397904676795437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8952393262265269784530291 13428589893397904676795437)
                  ·
                    refine ⟨5035721210024214253798289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13428589893397904676795437 5035721210024214253798289)
                    ·
                      refine ⟨3776790907518160690348717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5035721210024214253798289 3776790907518160690348717)
                      ·
                        rfl

theorem cell23_7355274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_7355274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355274 prefixEnd_7355274 := by exact prefixLift 7355274
  have htrace : WordTrace (prefixWord ++ tailWord_7355274) baseStart_7355274 baseEnd_7355274 := by
    simpa [prefixWord, tailWord_7355274, baseEnd_7355274] using wordTrace_append hprefix tailTrace_7355274
  have hstable : (prefixWord ++ tailWord_7355274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355274).length < 2 ^ (prefixWord ++ tailWord_7355274).sum := by decide
  have hdescent : baseEnd_7355274 < baseStart_7355274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355290 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5]
def baseStart_7355290 : Nat := 118140960795 + 7355290 * 2 ^ 59
def prefixEnd_7355290 : Nat := 4983230072969 + 3 ^ 40 * 7355290 * 2
def baseEnd_7355290 : Nat := 3776799123208632627748643

theorem tailTrace_7355290 : CollatzResearch.WordTrace tailWord_7355290 prefixEnd_7355290 3776799123208632627748643 := by
  unfold tailWord_7355290
  simp only [CollatzResearch.WordTrace]
  refine ⟨67067366380761997091807831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178846310348698658911487549 67067366380761997091807831)
  ·
    refine ⟨100601049571142995637711747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67067366380761997091807831 100601049571142995637711747)
    ·
      refine ⟨150901574356714493456567621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100601049571142995637711747 150901574356714493456567621)
      ·
        refine ⟨28294045191883967523106429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150901574356714493456567621 28294045191883967523106429)
        ·
          refine ⟨10610266946956487821164911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28294045191883967523106429 10610266946956487821164911)
          ·
            refine ⟨15915400420434731731747367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10610266946956487821164911 15915400420434731731747367)
            ·
              refine ⟨23873100630652097597621051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15915400420434731731747367 23873100630652097597621051)
              ·
                refine ⟨35809650945978146396431577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23873100630652097597621051 35809650945978146396431577)
                ·
                  refine ⟨26857238209483609797323683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35809650945978146396431577 26857238209483609797323683)
                  ·
                    refine ⟨40285857314225414695985525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26857238209483609797323683 40285857314225414695985525)
                    ·
                      refine ⟨3776799123208632627748643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40285857314225414695985525 3776799123208632627748643)
                      ·
                        rfl

theorem cell23_7355290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_7355290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355290 prefixEnd_7355290 := by exact prefixLift 7355290
  have htrace : WordTrace (prefixWord ++ tailWord_7355290) baseStart_7355290 baseEnd_7355290 := by
    simpa [prefixWord, tailWord_7355290, baseEnd_7355290] using wordTrace_append hprefix tailTrace_7355290
  have hstable : (prefixWord ++ tailWord_7355290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355290).length < 2 ^ (prefixWord ++ tailWord_7355290).sum := by decide
  have hdescent : baseEnd_7355290 < baseStart_7355290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355321 : List Nat := [1, 2, 1, 4, 2, 4, 2, 1, 2, 2, 2]
def baseStart_7355321 : Nat := 118140960795 + 7355321 * 2 ^ 59
def prefixEnd_7355321 : Nat := 4983230072969 + 3 ^ 40 * 7355321 * 2
def baseEnd_7355321 : Nat := 3776815041108922006461001

theorem tailTrace_7355321 : CollatzResearch.WordTrace tailWord_7355321 prefixEnd_7355321 3776815041108922006461001 := by
  unfold tailWord_7355321
  simp only [CollatzResearch.WordTrace]
  refine ⟨268270596185935680661609817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178847064123957120441073211 268270596185935680661609817)
  ·
    refine ⟨201202947139451760496207363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268270596185935680661609817 201202947139451760496207363)
    ·
      refine ⟨301804420709177640744311045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201202947139451760496207363 301804420709177640744311045)
      ·
        refine ⟨56588328882970807639558321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301804420709177640744311045 56588328882970807639558321)
        ·
          refine ⟨42441246662228105729668741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56588328882970807639558321 42441246662228105729668741)
          ·
            refine ⟨7957733749167769824312889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42441246662228105729668741 7957733749167769824312889)
            ·
              refine ⟨5968300311875827368234667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7957733749167769824312889 5968300311875827368234667)
              ·
                refine ⟨8952450467813741052352001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5968300311875827368234667 8952450467813741052352001)
                ·
                  refine ⟨6714337850860305789264001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8952450467813741052352001 6714337850860305789264001)
                  ·
                    refine ⟨5035753388145229341948001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6714337850860305789264001 5035753388145229341948001)
                    ·
                      refine ⟨3776815041108922006461001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5035753388145229341948001 3776815041108922006461001)
                      ·
                        rfl

theorem cell23_7355321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_7355321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355321 prefixEnd_7355321 := by exact prefixLift 7355321
  have htrace : WordTrace (prefixWord ++ tailWord_7355321) baseStart_7355321 baseEnd_7355321 := by
    simpa [prefixWord, tailWord_7355321, baseEnd_7355321] using wordTrace_append hprefix tailTrace_7355321
  have hstable : (prefixWord ++ tailWord_7355321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355321).length < 2 ^ (prefixWord ++ tailWord_7355321).sum := by decide
  have hdescent : baseEnd_7355321 < baseStart_7355321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355340 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 2, 5]
def baseStart_7355340 : Nat := 118140960795 + 7355340 * 2 ^ 59
def prefixEnd_7355340 : Nat := 4983230072969 + 3 ^ 40 * 7355340 * 2
def baseEnd_7355340 : Nat := 1258941599080452477374471

theorem tailTrace_7355340 : CollatzResearch.WordTrace tailWord_7355340 prefixEnd_7355340 1258941599080452477374471 := by
  unfold tailWord_7355340
  simp only [CollatzResearch.WordTrace]
  refine ⟨134135644586433423453275737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178847526115244564604367649 134135644586433423453275737)
  ·
    refine ⟨100601733439825067589956803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134135644586433423453275737 100601733439825067589956803)
    ·
      refine ⟨150902600159737601384935205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100601733439825067589956803 150902600159737601384935205)
      ·
        refine ⟨28294237529950800259675351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150902600159737601384935205 28294237529950800259675351)
        ·
          refine ⟨42441356294926200389513027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28294237529950800259675351 42441356294926200389513027)
          ·
            refine ⟨63662034442389300584269541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42441356294926200389513027 63662034442389300584269541)
            ·
              refine ⟨11936631457947993859550539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63662034442389300584269541 11936631457947993859550539)
              ·
                refine ⟨17904947186921990789325809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11936631457947993859550539 17904947186921990789325809)
                ·
                  refine ⟨13428710390191493091994357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17904947186921990789325809 13428710390191493091994357)
                  ·
                    refine ⟨1258941599080452477374471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13428710390191493091994357 1258941599080452477374471)
                    ·
                      rfl

theorem cell23_7355340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_7355340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355340 prefixEnd_7355340 := by exact prefixLift 7355340
  have htrace : WordTrace (prefixWord ++ tailWord_7355340) baseStart_7355340 baseEnd_7355340 := by
    simpa [prefixWord, tailWord_7355340, baseEnd_7355340] using wordTrace_append hprefix tailTrace_7355340
  have hstable : (prefixWord ++ tailWord_7355340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355340).length < 2 ^ (prefixWord ++ tailWord_7355340).sum := by decide
  have hdescent : baseEnd_7355340 < baseStart_7355340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355363 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 5]
def baseStart_7355363 : Nat := 118140960795 + 7355363 * 2 ^ 59
def prefixEnd_7355363 : Nat := 4983230072969 + 3 ^ 40 * 7355363 * 2
def baseEnd_7355363 : Nat := 3776836607296410842135807

theorem tailTrace_7355363 : CollatzResearch.WordTrace tailWord_7355363 prefixEnd_7355363 3776836607296410842135807 := by
  unfold tailWord_7355363
  simp only [CollatzResearch.WordTrace]
  refine ⟨268272128051783521834638743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178848085367855681223092495 268272128051783521834638743)
  ·
    refine ⟨402408192077675282751958115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268272128051783521834638743 402408192077675282751958115)
    ·
      refine ⟨603612288116512924127937173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402408192077675282751958115 603612288116512924127937173)
      ·
        refine ⟨28294326005461543318497055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 603612288116512924127937173 28294326005461543318497055)
        ·
          refine ⟨42441489008192314977745583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28294326005461543318497055 42441489008192314977745583)
          ·
            refine ⟨63662233512288472466618375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42441489008192314977745583 63662233512288472466618375)
            ·
              refine ⟨95493350268432708699927563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63662233512288472466618375 95493350268432708699927563)
              ·
                refine ⟨143240025402649063049891345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95493350268432708699927563 143240025402649063049891345)
                ·
                  refine ⟨107430019051986797287418509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143240025402649063049891345 107430019051986797287418509)
                  ·
                    refine ⟨40286257144495048982781941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107430019051986797287418509 40286257144495048982781941)
                    ·
                      refine ⟨3776836607296410842135807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40286257144495048982781941 3776836607296410842135807)
                      ·
                        rfl

theorem cell23_7355363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_7355363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355363 prefixEnd_7355363 := by exact prefixLift 7355363
  have htrace : WordTrace (prefixWord ++ tailWord_7355363) baseStart_7355363 baseEnd_7355363 := by
    simpa [prefixWord, tailWord_7355363, baseEnd_7355363] using wordTrace_append hprefix tailTrace_7355363
  have hstable : (prefixWord ++ tailWord_7355363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355363).length < 2 ^ (prefixWord ++ tailWord_7355363).sum := by decide
  have hdescent : baseEnd_7355363 < baseStart_7355363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355377 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 2, 4, 2]
def baseStart_7355377 : Nat := 118140960795 + 7355377 * 2 ^ 59
def prefixEnd_7355377 : Nat := 4983230072969 + 3 ^ 40 * 7355377 * 2
def baseEnd_7355377 : Nat := 3776843796025573787360743

theorem tailTrace_7355377 : CollatzResearch.WordTrace tailWord_7355377 prefixEnd_7355377 3776843796025573787360743 := by
  unfold tailWord_7355377
  simp only [CollatzResearch.WordTrace]
  refine ⟨268272638673732802225648385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178848425782488534817098923 268272638673732802225648385)
  ·
    refine ⟨201204479005299601669236289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268272638673732802225648385 201204479005299601669236289)
    ·
      refine ⟨150903359253974701251927217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201204479005299601669236289 150903359253974701251927217)
      ·
        refine ⟨113177519440481025938945413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150903359253974701251927217 113177519440481025938945413)
        ·
          refine ⟨21220784895090192363552265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113177519440481025938945413 21220784895090192363552265)
          ·
            refine ⟨15915588671317644272664199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21220784895090192363552265 15915588671317644272664199)
            ·
              refine ⟨23873383006976466408996299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15915588671317644272664199 23873383006976466408996299)
              ·
                refine ⟨35810074510464699613494449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23873383006976466408996299 35810074510464699613494449)
                ·
                  refine ⟨26857555882848524710120837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35810074510464699613494449 26857555882848524710120837)
                  ·
                    refine ⟨5035791728034098383147657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26857555882848524710120837 5035791728034098383147657)
                    ·
                      refine ⟨3776843796025573787360743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5035791728034098383147657 3776843796025573787360743)
                      ·
                        rfl

theorem cell23_7355377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_7355377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355377 prefixEnd_7355377 := by exact prefixLift 7355377
  have htrace : WordTrace (prefixWord ++ tailWord_7355377) baseStart_7355377 baseEnd_7355377 := by
    simpa [prefixWord, tailWord_7355377, baseEnd_7355377] using wordTrace_append hprefix tailTrace_7355377
  have hstable : (prefixWord ++ tailWord_7355377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355377).length < 2 ^ (prefixWord ++ tailWord_7355377).sum := by decide
  have hdescent : baseEnd_7355377 < baseStart_7355377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355394 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_7355394 : Nat := 118140960795 + 7355394 * 2 ^ 59
def prefixEnd_7355394 : Nat := 4983230072969 + 3 ^ 40 * 7355394 * 2
def baseEnd_7355394 : Nat := 3776852525196700220848165

theorem tailTrace_7355394 : CollatzResearch.WordTrace tailWord_7355394 prefixEnd_7355394 3776852525196700220848165 := by
  unfold tailWord_7355394
  simp only [CollatzResearch.WordTrace]
  refine ⟨67068314678667803532254309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178848839143114142752678157 67068314678667803532254309)
  ·
    refine ⟨12575309002250213162297683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67068314678667803532254309 12575309002250213162297683)
    ·
      refine ⟨18862963503375319743446525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12575309002250213162297683 18862963503375319743446525)
      ·
        refine ⟨7073611313765744903792447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18862963503375319743446525 7073611313765744903792447)
        ·
          refine ⟨10610416970648617355688671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7073611313765744903792447 10610416970648617355688671)
          ·
            refine ⟨15915625455972926033533007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10610416970648617355688671 15915625455972926033533007)
            ·
              refine ⟨23873438183959389050299511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15915625455972926033533007 23873438183959389050299511)
              ·
                refine ⟨35810157275939083575449267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23873438183959389050299511 35810157275939083575449267)
                ·
                  refine ⟨53715235913908625363173901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35810157275939083575449267 53715235913908625363173901)
                  ·
                    refine ⟨20143213467715734511190213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53715235913908625363173901 20143213467715734511190213)
                    ·
                      refine ⟨3776852525196700220848165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20143213467715734511190213 3776852525196700220848165)
                      ·
                        rfl

theorem cell23_7355394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_7355394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355394 prefixEnd_7355394 := by exact prefixLift 7355394
  have htrace : WordTrace (prefixWord ++ tailWord_7355394) baseStart_7355394 baseEnd_7355394 := by
    simpa [prefixWord, tailWord_7355394, baseEnd_7355394] using wordTrace_append hprefix tailTrace_7355394
  have hstable : (prefixWord ++ tailWord_7355394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355394).length < 2 ^ (prefixWord ++ tailWord_7355394).sum := by decide
  have hdescent : baseEnd_7355394 < baseStart_7355394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355404 : List Nat := [2, 2, 1, 2, 3, 3, 2, 3, 1, 4]
def baseStart_7355404 : Nat := 118140960795 + 7355404 * 2 ^ 59
def prefixEnd_7355404 : Nat := 4983230072969 + 3 ^ 40 * 7355404 * 2
def baseEnd_7355404 : Nat := 1258952553334415060574373

theorem tailTrace_7355404 : CollatzResearch.WordTrace tailWord_7355404 prefixEnd_7355404 1258952553334415060574373 := by
  unfold tailWord_7355404
  simp only [CollatzResearch.WordTrace]
  refine ⟨134136811722317492918440633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178849082296423323891254177 134136811722317492918440633)
  ·
    refine ⟨100602608791738119688830475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134136811722317492918440633 100602608791738119688830475)
    ·
      refine ⟨150903913187607179533245713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100602608791738119688830475 150903913187607179533245713)
      ·
        refine ⟨113177934890705384649934285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150903913187607179533245713 113177934890705384649934285)
        ·
          refine ⟨42441725584014519243725357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113177934890705384649934285 42441725584014519243725357)
          ·
            refine ⟨15915647094005444716397009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42441725584014519243725357 15915647094005444716397009)
            ·
              refine ⟨11936735320504083537297757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15915647094005444716397009 11936735320504083537297757)
              ·
                refine ⟨4476275745189031326486659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11936735320504083537297757 4476275745189031326486659)
                ·
                  refine ⟨6714413617783546989729989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476275745189031326486659 6714413617783546989729989)
                  ·
                    refine ⟨1258952553334415060574373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6714413617783546989729989 1258952553334415060574373)
                    ·
                      rfl

theorem cell23_7355404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_7355404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355404 prefixEnd_7355404 := by exact prefixLift 7355404
  have htrace : WordTrace (prefixWord ++ tailWord_7355404) baseStart_7355404 baseEnd_7355404 := by
    simpa [prefixWord, tailWord_7355404, baseEnd_7355404] using wordTrace_append hprefix tailTrace_7355404
  have hstable : (prefixWord ++ tailWord_7355404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355404).length < 2 ^ (prefixWord ++ tailWord_7355404).sum := by decide
  have hdescent : baseEnd_7355404 < baseStart_7355404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355427 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 3, 1, 3]
def baseStart_7355427 : Nat := 118140960795 + 7355427 * 2 ^ 59
def prefixEnd_7355427 : Nat := 4983230072969 + 3 ^ 40 * 7355427 * 2
def baseEnd_7355427 : Nat := 3776869470058298591735513

theorem tailTrace_7355427 : CollatzResearch.WordTrace tailWord_7355427 prefixEnd_7355427 3776869470058298591735513 := by
  unfold tailWord_7355427
  simp only [CollatzResearch.WordTrace]
  refine ⟨268274462323551660764968535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178849641549034440509979023 268274462323551660764968535)
  ·
    refine ⟨402411693485327491147452803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268274462323551660764968535 402411693485327491147452803)
    ·
      refine ⟨603617540227991236721179205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402411693485327491147452803 603617540227991236721179205)
      ·
        refine ⟨113178288792748356885221101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 603617540227991236721179205 113178288792748356885221101)
        ·
          refine ⟨42441858297280633831957913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113178288792748356885221101 42441858297280633831957913)
          ·
            refine ⟨31831393722960475373968435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42441858297280633831957913 31831393722960475373968435)
            ·
              refine ⟨47747090584440713060952653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31831393722960475373968435 47747090584440713060952653)
              ·
                refine ⟨17905158969165267397857245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47747090584440713060952653 17905158969165267397857245)
                ·
                  refine ⟨6714434613436975274196467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17905158969165267397857245 6714434613436975274196467)
                  ·
                    refine ⟨10071651920155462911294701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6714434613436975274196467 10071651920155462911294701)
                    ·
                      refine ⟨3776869470058298591735513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10071651920155462911294701 3776869470058298591735513)
                      ·
                        rfl

theorem cell23_7355427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_7355427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355427 prefixEnd_7355427 := by exact prefixLift 7355427
  have htrace : WordTrace (prefixWord ++ tailWord_7355427) baseStart_7355427 baseEnd_7355427 := by
    simpa [prefixWord, tailWord_7355427, baseEnd_7355427] using wordTrace_append hprefix tailTrace_7355427
  have hstable : (prefixWord ++ tailWord_7355427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355427).length < 2 ^ (prefixWord ++ tailWord_7355427).sum := by decide
  have hdescent : baseEnd_7355427 < baseStart_7355427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355434 : List Nat := [3, 1, 4, 1, 3, 1, 3, 1, 6]
def baseStart_7355434 : Nat := 118140960795 + 7355434 * 2 ^ 59
def prefixEnd_7355434 : Nat := 4983230072969 + 3 ^ 40 * 7355434 * 2
def baseEnd_7355434 : Nat := 419652562713653340483109

theorem tailTrace_7355434 : CollatzResearch.WordTrace tailWord_7355434 prefixEnd_7355434 419652562713653340483109 := by
  unfold tailWord_7355434
  simp only [CollatzResearch.WordTrace]
  refine ⟨67068679408631575240118339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178849811756350867306982237 67068679408631575240118339)
  ·
    refine ⟨100603019112947362860177509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67068679408631575240118339 100603019112947362860177509)
    ·
      refine ⟨18863066083677630536283283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100603019112947362860177509 18863066083677630536283283)
      ·
        refine ⟨28294599125516445804424925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18863066083677630536283283 28294599125516445804424925)
        ·
          refine ⟨10610474672068667176659347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28294599125516445804424925 10610474672068667176659347)
          ·
            refine ⟨15915712008103000764989021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10610474672068667176659347 15915712008103000764989021)
            ·
              refine ⟨5968392003038625286870883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15915712008103000764989021 5968392003038625286870883)
              ·
                refine ⟨8952588004557937930306325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5968392003038625286870883 8952588004557937930306325)
                ·
                  refine ⟨419652562713653340483109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8952588004557937930306325 419652562713653340483109)
                  ·
                    rfl

theorem cell23_7355434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 6].length) (baseStart_7355434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355434 prefixEnd_7355434 := by exact prefixLift 7355434
  have htrace : WordTrace (prefixWord ++ tailWord_7355434) baseStart_7355434 baseEnd_7355434 := by
    simpa [prefixWord, tailWord_7355434, baseEnd_7355434] using wordTrace_append hprefix tailTrace_7355434
  have hstable : (prefixWord ++ tailWord_7355434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355434).length < 2 ^ (prefixWord ++ tailWord_7355434).sum := by decide
  have hdescent : baseEnd_7355434 < baseStart_7355434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355450 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4]
def baseStart_7355450 : Nat := 118140960795 + 7355450 * 2 ^ 59
def prefixEnd_7355450 : Nat := 4983230072969 + 3 ^ 40 * 7355450 * 2
def baseEnd_7355450 : Nat := 3776881280113352001747907

theorem tailTrace_7355450 : CollatzResearch.WordTrace tailWord_7355450 prefixEnd_7355450 3776881280113352001747907 := by
  unfold tailWord_7355450
  simp only [CollatzResearch.WordTrace]
  refine ⟨67068825300617083923263951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178850200801645557128703869 67068825300617083923263951)
  ·
    refine ⟨100603237950925625884895927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67068825300617083923263951 100603237950925625884895927)
    ·
      refine ⟨150904856926388438827343891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100603237950925625884895927 150904856926388438827343891)
      ·
        refine ⟨226357285389582658241015837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150904856926388438827343891 226357285389582658241015837)
        ·
          refine ⟨84883982021093496840380939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226357285389582658241015837 84883982021093496840380939)
          ·
            refine ⟨127325973031640245260571409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84883982021093496840380939 127325973031640245260571409)
            ·
              refine ⟨95494479773730183945428557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127325973031640245260571409 95494479773730183945428557)
              ·
                refine ⟨35810429915148818979535709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95494479773730183945428557 35810429915148818979535709)
                ·
                  refine ⟨13428911218180807117325891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35810429915148818979535709 13428911218180807117325891)
                  ·
                    refine ⟨20143366827271210675988837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13428911218180807117325891 20143366827271210675988837)
                    ·
                      refine ⟨3776881280113352001747907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20143366827271210675988837 3776881280113352001747907)
                      ·
                        rfl

theorem cell23_7355450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_7355450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355450 prefixEnd_7355450 := by exact prefixLift 7355450
  have htrace : WordTrace (prefixWord ++ tailWord_7355450) baseStart_7355450 baseEnd_7355450 := by
    simpa [prefixWord, tailWord_7355450, baseEnd_7355450] using wordTrace_append hprefix tailTrace_7355450
  have hstable : (prefixWord ++ tailWord_7355450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355450).length < 2 ^ (prefixWord ++ tailWord_7355450).sum := by decide
  have hdescent : baseEnd_7355450 < baseStart_7355450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355454 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_7355454 : Nat := 118140960795 + 7355454 * 2 ^ 59
def prefixEnd_7355454 : Nat := 4983230072969 + 3 ^ 40 * 7355454 * 2
def baseEnd_7355454 : Nat := 3776883334035969986097889

theorem tailTrace_7355454 : CollatzResearch.WordTrace tailWord_7355454 prefixEnd_7355454 3776883334035969986097889 := by
  unfold tailWord_7355454
  simp only [CollatzResearch.WordTrace]
  refine ⟨33534430886806730547025177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178850298062969229584134277 33534430886806730547025177)
  ·
    refine ⟨25150823165105047910268883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33534430886806730547025177 25150823165105047910268883)
    ·
      refine ⟨37726234747657571865403325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25150823165105047910268883 37726234747657571865403325)
      ·
        refine ⟨14147338030371589449526247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37726234747657571865403325 14147338030371589449526247)
        ·
          refine ⟨21221007045557384174289371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14147338030371589449526247 21221007045557384174289371)
          ·
            refine ⟨31831510568336076261434057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21221007045557384174289371 31831510568336076261434057)
            ·
              refine ⟨23873632926252057196075543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31831510568336076261434057 23873632926252057196075543)
              ·
                refine ⟨35810449389378085794113315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23873632926252057196075543 35810449389378085794113315)
                ·
                  refine ⟨53715674084067128691169973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35810449389378085794113315 53715674084067128691169973)
                  ·
                    refine ⟨5035844445381293314797185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53715674084067128691169973 5035844445381293314797185)
                    ·
                      refine ⟨3776883334035969986097889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5035844445381293314797185 3776883334035969986097889)
                      ·
                        rfl

theorem cell23_7355454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_7355454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355454 prefixEnd_7355454 := by exact prefixLift 7355454
  have htrace : WordTrace (prefixWord ++ tailWord_7355454) baseStart_7355454 baseEnd_7355454 := by
    simpa [prefixWord, tailWord_7355454, baseEnd_7355454] using wordTrace_append hprefix tailTrace_7355454
  have hstable : (prefixWord ++ tailWord_7355454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355454).length < 2 ^ (prefixWord ++ tailWord_7355454).sum := by decide
  have hdescent : baseEnd_7355454 < baseStart_7355454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355473 : List Nat := [1, 2, 2, 1, 3, 1, 13]
def baseStart_7355473 : Nat := 118140960795 + 7355473 * 2 ^ 59
def prefixEnd_7355473 : Nat := 4983230072969 + 3 ^ 40 * 7355473 * 2
def baseEnd_7355473 : Nat := 46628309755165498910621

theorem tailTrace_7355473 : CollatzResearch.WordTrace tailWord_7355473 prefixEnd_7355473 46628309755165498910621 := by
  unfold tailWord_7355473
  simp only [CollatzResearch.WordTrace]
  refine ⟨268276140081385010621143073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178850760054256673747428715 268276140081385010621143073)
  ·
    refine ⟨201207105061038757965857305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268276140081385010621143073 201207105061038757965857305)
    ·
      refine ⟨150905328795779068474392979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201207105061038757965857305 150905328795779068474392979)
      ·
        refine ⟨226357993193668602711589469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150905328795779068474392979 226357993193668602711589469)
        ·
          refine ⟨84884247447625726016846051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226357993193668602711589469 84884247447625726016846051)
          ·
            refine ⟨127326371171438589025269077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84884247447625726016846051 127326371171438589025269077)
            ·
              refine ⟨46628309755165498910621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 127326371171438589025269077 46628309755165498910621)
              ·
                rfl

theorem cell23_7355473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 13].length) (baseStart_7355473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355473 prefixEnd_7355473 := by exact prefixLift 7355473
  have htrace : WordTrace (prefixWord ++ tailWord_7355473) baseStart_7355473 baseEnd_7355473 := by
    simpa [prefixWord, tailWord_7355473, baseEnd_7355473] using wordTrace_append hprefix tailTrace_7355473
  have hstable : (prefixWord ++ tailWord_7355473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355473).length < 2 ^ (prefixWord ++ tailWord_7355473).sum := by decide
  have hdescent : baseEnd_7355473 < baseStart_7355473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355477 : List Nat := [1, 3, 2, 2, 1, 2, 2, 4, 2, 4]
def baseStart_7355477 : Nat := 118140960795 + 7355477 * 2 ^ 59
def prefixEnd_7355477 : Nat := 4983230072969 + 3 ^ 40 * 7355477 * 2
def baseEnd_7355477 : Nat := 1258965048030341132036761

theorem tailTrace_7355477 : CollatzResearch.WordTrace tailWord_7355477 prefixEnd_7355477 1258965048030341132036761 := by
  unfold tailWord_7355477
  simp only [CollatzResearch.WordTrace]
  refine ⟨268276285973370519304288685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178850857315580346202859123 268276285973370519304288685)
  ·
    refine ⟨100603607240013944739108257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268276285973370519304288685 100603607240013944739108257)
    ·
      refine ⟨75452705430010458554331193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100603607240013944739108257 75452705430010458554331193)
      ·
        refine ⟨56589529072507843915748395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75452705430010458554331193 56589529072507843915748395)
        ·
          refine ⟨84884293608761765873622593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56589529072507843915748395 84884293608761765873622593)
          ·
            refine ⟨63663220206571324405216945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84884293608761765873622593 63663220206571324405216945)
            ·
              refine ⟨47747415154928493303912709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63663220206571324405216945 47747415154928493303912709)
              ·
                refine ⟨8952640341549092494483633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47747415154928493303912709 8952640341549092494483633)
                ·
                  refine ⟨6714480256161819370862725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8952640341549092494483633 6714480256161819370862725)
                  ·
                    refine ⟨1258965048030341132036761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6714480256161819370862725 1258965048030341132036761)
                    ·
                      rfl

theorem cell23_7355477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_7355477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355477 prefixEnd_7355477 := by exact prefixLift 7355477
  have htrace : WordTrace (prefixWord ++ tailWord_7355477) baseStart_7355477 baseEnd_7355477 := by
    simpa [prefixWord, tailWord_7355477, baseEnd_7355477] using wordTrace_append hprefix tailTrace_7355477
  have hstable : (prefixWord ++ tailWord_7355477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355477).length < 2 ^ (prefixWord ++ tailWord_7355477).sum := by decide
  have hdescent : baseEnd_7355477 < baseStart_7355477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355517 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_7355517 : Nat := 118140960795 + 7355517 * 2 ^ 59
def prefixEnd_7355517 : Nat := 4983230072969 + 3 ^ 40 * 7355517 * 2
def baseEnd_7355517 : Nat := 3776915683317203239610099

theorem tailTrace_7355517 : CollatzResearch.WordTrace tailWord_7355517 prefixEnd_7355517 3776915683317203239610099 := by
  unfold tailWord_7355517
  simp only [CollatzResearch.WordTrace]
  refine ⟨268277744893225606135744805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178851829928817070757163203 268277744893225606135744805)
  ·
    refine ⟨50302077167479801150452151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268277744893225606135744805 50302077167479801150452151)
    ·
      refine ⟨75453115751219701725678227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50302077167479801150452151 75453115751219701725678227)
      ·
        refine ⟨113179673626829552588517341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75453115751219701725678227 113179673626829552588517341)
        ·
          refine ⟨42442377610061082220694003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113179673626829552588517341 42442377610061082220694003)
          ·
            refine ⟨63663566415091623331041005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42442377610061082220694003 63663566415091623331041005)
            ·
              refine ⟨23873837405659358749140377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63663566415091623331041005 23873837405659358749140377)
              ·
                refine ⟨17905378054244519061855283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23873837405659358749140377 17905378054244519061855283)
                ·
                  refine ⟨26858067081366778592782925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17905378054244519061855283 26858067081366778592782925)
                  ·
                    refine ⟨10071775155512541972293597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26858067081366778592782925 10071775155512541972293597)
                    ·
                      refine ⟨3776915683317203239610099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10071775155512541972293597 3776915683317203239610099)
                      ·
                        rfl

theorem cell23_7355517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_7355517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355517 prefixEnd_7355517 := by exact prefixLift 7355517
  have htrace : WordTrace (prefixWord ++ tailWord_7355517) baseStart_7355517 baseEnd_7355517 := by
    simpa [prefixWord, tailWord_7355517, baseEnd_7355517] using wordTrace_append hprefix tailTrace_7355517
  have hstable : (prefixWord ++ tailWord_7355517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355517).length < 2 ^ (prefixWord ++ tailWord_7355517).sum := by decide
  have hdescent : baseEnd_7355517 < baseStart_7355517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355521 : List Nat := [1, 2, 4, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_7355521 : Nat := 118140960795 + 7355521 * 2 ^ 59
def prefixEnd_7355521 : Nat := 4983230072969 + 3 ^ 40 * 7355521 * 2
def baseEnd_7355521 : Nat := 3776917737239821223960081

theorem tailTrace_7355521 : CollatzResearch.WordTrace tailWord_7355521 prefixEnd_7355521 3776917737239821223960081 := by
  unfold tailWord_7355521
  simp only [CollatzResearch.WordTrace]
  refine ⟨268277890785211114818890417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178851927190140743212593611 268277890785211114818890417)
  ·
    refine ⟨201208418088908336114167813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268277890785211114818890417 201208418088908336114167813)
    ·
      refine ⟨37726578391670313021406465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201208418088908336114167813 37726578391670313021406465)
      ·
        refine ⟨28294933793752734766054849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37726578391670313021406465 28294933793752734766054849)
        ·
          refine ⟨21221200345314551074541137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28294933793752734766054849 21221200345314551074541137)
          ·
            refine ⟨15915900258985913305905853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21221200345314551074541137 15915900258985913305905853)
            ·
              refine ⟨5968462597119717489714695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15915900258985913305905853 5968462597119717489714695)
              ·
                refine ⟨8952693895679576234572043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5968462597119717489714695 8952693895679576234572043)
                ·
                  refine ⟨13429040843519364351858065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8952693895679576234572043 13429040843519364351858065)
                  ·
                    refine ⟨10071780632639523263893549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13429040843519364351858065 10071780632639523263893549)
                    ·
                      refine ⟨3776917737239821223960081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10071780632639523263893549 3776917737239821223960081)
                      ·
                        rfl

theorem cell23_7355521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_7355521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355521 prefixEnd_7355521 := by exact prefixLift 7355521
  have htrace : WordTrace (prefixWord ++ tailWord_7355521) baseStart_7355521 baseEnd_7355521 := by
    simpa [prefixWord, tailWord_7355521, baseEnd_7355521] using wordTrace_append hprefix tailTrace_7355521
  have hstable : (prefixWord ++ tailWord_7355521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355521).length < 2 ^ (prefixWord ++ tailWord_7355521).sum := by decide
  have hdescent : baseEnd_7355521 < baseStart_7355521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355544 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 3, 3, 2]
def baseStart_7355544 : Nat := 118140960795 + 7355544 * 2 ^ 59
def prefixEnd_7355544 : Nat := 4983230072969 + 3 ^ 40 * 7355544 * 2
def baseEnd_7355544 : Nat := 3776929547294874633972475

theorem tailTrace_7355544 : CollatzResearch.WordTrace tailWord_7355544 prefixEnd_7355544 3776929547294874633972475 := by
  unfold tailWord_7355544
  simp only [CollatzResearch.WordTrace]
  refine ⟨134139364832063894873488843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178852486442751859831318457 134139364832063894873488843)
  ·
    refine ⟨201209047248095842310233265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134139364832063894873488843 201209047248095842310233265)
    ·
      refine ⟨150906785436071881732674949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201209047248095842310233265 150906785436071881732674949)
      ·
        refine ⟨28295022269263477824876553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150906785436071881732674949 28295022269263477824876553)
        ·
          refine ⟨21221266701947608368657415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28295022269263477824876553 21221266701947608368657415)
          ·
            refine ⟨31831900052921412552986123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21221266701947608368657415 31831900052921412552986123)
            ·
              refine ⟨47747850079382118829479185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31831900052921412552986123 47747850079382118829479185)
              ·
                refine ⟨35810887559536589122109389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47747850079382118829479185 35810887559536589122109389)
                ·
                  refine ⟨13429082834826220920791021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35810887559536589122109389 13429082834826220920791021)
                  ·
                    refine ⟨5035906063059832845296633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13429082834826220920791021 5035906063059832845296633)
                    ·
                      refine ⟨3776929547294874633972475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5035906063059832845296633 3776929547294874633972475)
                      ·
                        rfl

theorem cell23_7355544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_7355544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355544 prefixEnd_7355544 := by exact prefixLift 7355544
  have htrace : WordTrace (prefixWord ++ tailWord_7355544) baseStart_7355544 baseEnd_7355544 := by
    simpa [prefixWord, tailWord_7355544, baseEnd_7355544] using wordTrace_append hprefix tailTrace_7355544
  have hstable : (prefixWord ++ tailWord_7355544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355544).length < 2 ^ (prefixWord ++ tailWord_7355544).sum := by decide
  have hdescent : baseEnd_7355544 < baseStart_7355544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355607 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 3]
def baseStart_7355607 : Nat := 118140960795 + 7355607 * 2 ^ 59
def prefixEnd_7355607 : Nat := 4983230072969 + 3 ^ 40 * 7355607 * 2
def baseEnd_7355607 : Nat := 3776961896576107887484685

theorem tailTrace_7355607 : CollatzResearch.WordTrace tailWord_7355607 prefixEnd_7355607 3776961896576107887484685 := by
  unfold tailWord_7355607
  simp only [CollatzResearch.WordTrace]
  refine ⟨268281027462899551506521075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178854018308599701004347383 268281027462899551506521075)
  ·
    refine ⟨402421541194349327259781613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268281027462899551506521075 402421541194349327259781613)
    ·
      refine ⟨150908077947880997722418105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402421541194349327259781613 150908077947880997722418105)
      ·
        refine ⟨113181058460910748291813579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150908077947880997722418105 113181058460910748291813579)
        ·
          refine ⟨169771587691366122437720369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113181058460910748291813579 169771587691366122437720369)
          ·
            refine ⟨127328690768524591828290277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169771587691366122437720369 127328690768524591828290277)
            ·
              refine ⟨23874129519098360967804427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127328690768524591828290277 23874129519098360967804427)
              ·
                refine ⟨35811194278647541451706641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23874129519098360967804427 35811194278647541451706641)
                ·
                  refine ⟨26858395708985656088779981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35811194278647541451706641 26858395708985656088779981)
                  ·
                    refine ⟨10071898390869621033292493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26858395708985656088779981 10071898390869621033292493)
                    ·
                      refine ⟨3776961896576107887484685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10071898390869621033292493 3776961896576107887484685)
                      ·
                        rfl

theorem cell23_7355607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_7355607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355607 prefixEnd_7355607 := by exact prefixLift 7355607
  have htrace : WordTrace (prefixWord ++ tailWord_7355607) baseStart_7355607 baseEnd_7355607 := by
    simpa [prefixWord, tailWord_7355607, baseEnd_7355607] using wordTrace_append hprefix tailTrace_7355607
  have hstable : (prefixWord ++ tailWord_7355607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355607).length < 2 ^ (prefixWord ++ tailWord_7355607).sum := by decide
  have hdescent : baseEnd_7355607 < baseStart_7355607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355608 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 1, 4, 2]
def baseStart_7355608 : Nat := 118140960795 + 7355608 * 2 ^ 59
def prefixEnd_7355608 : Nat := 4983230072969 + 3 ^ 40 * 7355608 * 2
def baseEnd_7355608 : Nat := 3776962410056762383572181

theorem tailTrace_7355608 : CollatzResearch.WordTrace tailWord_7355608 prefixEnd_7355608 3776962410056762383572181 := by
  unfold tailWord_7355608
  simp only [CollatzResearch.WordTrace]
  refine ⟨134140531967947964338653739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178854042623930619118204985 134140531967947964338653739)
  ·
    refine ⟨201210797951921946507980609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134140531967947964338653739 201210797951921946507980609)
    ·
      refine ⟨150908098463941459880985457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201210797951921946507980609 150908098463941459880985457)
      ·
        refine ⟨113181073847956094910739093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150908098463941459880985457 113181073847956094910739093)
        ·
          refine ⟨5305362836622941948940895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113181073847956094910739093 5305362836622941948940895)
          ·
            refine ⟨7958044254934412923411343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5305362836622941948940895 7958044254934412923411343)
            ·
              refine ⟨11937066382401619385117015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7958044254934412923411343 11937066382401619385117015)
              ·
                refine ⟨17905599573602429077675523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11937066382401619385117015 17905599573602429077675523)
                ·
                  refine ⟨26858399360403643616513285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17905599573602429077675523 26858399360403643616513285)
                  ·
                    refine ⟨5035949880075683178096241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26858399360403643616513285 5035949880075683178096241)
                    ·
                      refine ⟨3776962410056762383572181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5035949880075683178096241 3776962410056762383572181)
                      ·
                        rfl

theorem cell23_7355608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_7355608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355608 prefixEnd_7355608 := by exact prefixLift 7355608
  have htrace : WordTrace (prefixWord ++ tailWord_7355608) baseStart_7355608 baseEnd_7355608 := by
    simpa [prefixWord, tailWord_7355608, baseEnd_7355608] using wordTrace_append hprefix tailTrace_7355608
  have hstable : (prefixWord ++ tailWord_7355608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355608).length < 2 ^ (prefixWord ++ tailWord_7355608).sum := by decide
  have hdescent : baseEnd_7355608 < baseStart_7355608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355631 : List Nat := [1, 1, 2, 1, 7, 2, 1, 3, 5]
def baseStart_7355631 : Nat := 118140960795 + 7355631 * 2 ^ 59
def prefixEnd_7355631 : Nat := 4983230072969 + 3 ^ 40 * 7355631 * 2
def baseEnd_7355631 : Nat := 419663802234646199287175

theorem tailTrace_7355631 : CollatzResearch.WordTrace tailWord_7355631 prefixEnd_7355631 419663802234646199287175 := by
  unfold tailWord_7355631
  simp only [CollatzResearch.WordTrace]
  refine ⟨268281902814812603605394747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178854601876541735736929831 268281902814812603605394747)
  ·
    refine ⟨402422854222218905408092121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268281902814812603605394747 402422854222218905408092121)
    ·
      refine ⟨301817140666664179056069091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402422854222218905408092121 301817140666664179056069091)
      ·
        refine ⟨452725710999996268584103637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301817140666664179056069091 452725710999996268584103637)
        ·
          refine ⟨10610758851562412544939929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 452725710999996268584103637 10610758851562412544939929)
          ·
            refine ⟨7958069138671809408704947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10610758851562412544939929 7958069138671809408704947)
            ·
              refine ⟨11937103708007714113057421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7958069138671809408704947 11937103708007714113057421)
              ·
                refine ⟨4476413890502892792396533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11937103708007714113057421 4476413890502892792396533)
                ·
                  refine ⟨419663802234646199287175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4476413890502892792396533 419663802234646199287175)
                  ·
                    rfl

theorem cell23_7355631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 5].length) (baseStart_7355631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355631 prefixEnd_7355631 := by exact prefixLift 7355631
  have htrace : WordTrace (prefixWord ++ tailWord_7355631) baseStart_7355631 baseEnd_7355631 := by
    simpa [prefixWord, tailWord_7355631, baseEnd_7355631] using wordTrace_append hprefix tailTrace_7355631
  have hstable : (prefixWord ++ tailWord_7355631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355631).length < 2 ^ (prefixWord ++ tailWord_7355631).sum := by decide
  have hdescent : baseEnd_7355631 < baseStart_7355631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355644 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 2, 5]
def baseStart_7355644 : Nat := 118140960795 + 7355644 * 2 ^ 59
def prefixEnd_7355644 : Nat := 4983230072969 + 3 ^ 40 * 7355644 * 2
def baseEnd_7355644 : Nat := 1258993631786774747574005

theorem tailTrace_7355644 : CollatzResearch.WordTrace tailWord_7355644 prefixEnd_7355644 1258993631786774747574005 := by
  unfold tailWord_7355644
  simp only [CollatzResearch.WordTrace]
  refine ⟨134141188481882753412808993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178854917975843671217078657 134141188481882753412808993)
  ·
    refine ⟨100605891361412065059606745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134141188481882753412808993 100605891361412065059606745)
    ·
      refine ⟨75454418521059048794705059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100605891361412065059606745 75454418521059048794705059)
      ·
        refine ⟨113181627781588573192057589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75454418521059048794705059 113181627781588573192057589)
        ·
          refine ⟨10610777604523928736755399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113181627781588573192057589 10610777604523928736755399)
          ·
            refine ⟨15916166406785893105133099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10610777604523928736755399 15916166406785893105133099)
            ·
              refine ⟨23874249610178839657699649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15916166406785893105133099 23874249610178839657699649)
              ·
                refine ⟨17905687207634129743274737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23874249610178839657699649 17905687207634129743274737)
                ·
                  refine ⟨13429265405725597307456053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17905687207634129743274737 13429265405725597307456053)
                  ·
                    refine ⟨1258993631786774747574005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13429265405725597307456053 1258993631786774747574005)
                    ·
                      rfl

theorem cell23_7355644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_7355644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355644 prefixEnd_7355644 := by exact prefixLift 7355644
  have htrace : WordTrace (prefixWord ++ tailWord_7355644) baseStart_7355644 baseEnd_7355644 := by
    simpa [prefixWord, tailWord_7355644, baseEnd_7355644] using wordTrace_append hprefix tailTrace_7355644
  have hstable : (prefixWord ++ tailWord_7355644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355644).length < 2 ^ (prefixWord ++ tailWord_7355644).sum := by decide
  have hdescent : baseEnd_7355644 < baseStart_7355644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355647 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 4]
def baseStart_7355647 : Nat := 118140960795 + 7355647 * 2 ^ 59
def prefixEnd_7355647 : Nat := 4983230072969 + 3 ^ 40 * 7355647 * 2
def baseEnd_7355647 : Nat := 3776982435802287730984501

theorem tailTrace_7355647 : CollatzResearch.WordTrace tailWord_7355647 prefixEnd_7355647 3776982435802287730984501 := by
  unfold tailWord_7355647
  simp only [CollatzResearch.WordTrace]
  refine ⟨268282486382754638337977195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178854990921836425558651463 268282486382754638337977195)
  ·
    refine ⟨402423729574131957506965793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268282486382754638337977195 402423729574131957506965793)
    ·
      refine ⟨301817797180598968130224345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402423729574131957506965793 301817797180598968130224345)
      ·
        refine ⟨226363347885449226097668259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301817797180598968130224345 226363347885449226097668259)
        ·
          refine ⟨339545021828173839146502389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226363347885449226097668259 339545021828173839146502389)
          ·
            refine ⟨31832345796391297419984599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 339545021828173839146502389 31832345796391297419984599)
            ·
              refine ⟨47748518694586946129976899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31832345796391297419984599 47748518694586946129976899)
              ·
                refine ⟨71622778041880419194965349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47748518694586946129976899 71622778041880419194965349)
                ·
                  refine ⟨13429270882852578599056003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71622778041880419194965349 13429270882852578599056003)
                  ·
                    refine ⟨20143906324278867898584005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13429270882852578599056003 20143906324278867898584005)
                    ·
                      refine ⟨3776982435802287730984501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20143906324278867898584005 3776982435802287730984501)
                      ·
                        rfl

theorem cell23_7355647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_7355647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355647 prefixEnd_7355647 := by exact prefixLift 7355647
  have htrace : WordTrace (prefixWord ++ tailWord_7355647) baseStart_7355647 baseEnd_7355647 := by
    simpa [prefixWord, tailWord_7355647, baseEnd_7355647] using wordTrace_append hprefix tailTrace_7355647
  have hstable : (prefixWord ++ tailWord_7355647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355647).length < 2 ^ (prefixWord ++ tailWord_7355647).sum := by decide
  have hdescent : baseEnd_7355647 < baseStart_7355647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355678 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_7355678 : Nat := 118140960795 + 7355678 * 2 ^ 59
def prefixEnd_7355678 : Nat := 4983230072969 + 3 ^ 40 * 7355678 * 2
def baseEnd_7355678 : Nat := 1258999451234192369898953

theorem tailTrace_7355678 : CollatzResearch.WordTrace tailWord_7355678 prefixEnd_7355678 1258999451234192369898953 := by
  unfold tailWord_7355678
  simp only [CollatzResearch.WordTrace]
  refine ⟨33535452130705291329044461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178855744697094887088237125 33535452130705291329044461)
  ·
    refine ⟨12575794549014484248391673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33535452130705291329044461 12575794549014484248391673)
    ·
      refine ⟨9431845911760863186293755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12575794549014484248391673 9431845911760863186293755)
      ·
        refine ⟨14147768867641294779440633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9431845911760863186293755 14147768867641294779440633)
        ·
          refine ⟨10610826650730971084580475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14147768867641294779440633 10610826650730971084580475)
          ·
            refine ⟨15916239976096456626870713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10610826650730971084580475 15916239976096456626870713)
            ·
              refine ⟨11937179982072342470153035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15916239976096456626870713 11937179982072342470153035)
              ·
                refine ⟨17905769973108513705229553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11937179982072342470153035 17905769973108513705229553)
                ·
                  refine ⟨13429327479831385278922165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17905769973108513705229553 13429327479831385278922165)
                  ·
                    refine ⟨1258999451234192369898953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13429327479831385278922165 1258999451234192369898953)
                    ·
                      rfl

theorem cell23_7355678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_7355678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355678 prefixEnd_7355678 := by exact prefixLift 7355678
  have htrace : WordTrace (prefixWord ++ tailWord_7355678) baseStart_7355678 baseEnd_7355678 := by
    simpa [prefixWord, tailWord_7355678, baseEnd_7355678] using wordTrace_append hprefix tailTrace_7355678
  have hstable : (prefixWord ++ tailWord_7355678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355678).length < 2 ^ (prefixWord ++ tailWord_7355678).sum := by decide
  have hdescent : baseEnd_7355678 < baseStart_7355678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355708 : List Nat := [2, 2, 2, 2, 1, 3, 4, 2, 1, 4]
def baseStart_7355708 : Nat := 118140960795 + 7355708 * 2 ^ 59
def prefixEnd_7355708 : Nat := 4983230072969 + 3 ^ 40 * 7355708 * 2
def baseEnd_7355708 : Nat := 1259004586040737330773907

theorem tailTrace_7355708 : CollatzResearch.WordTrace tailWord_7355708 prefixEnd_7355708 1259004586040737330773907 := by
  unfold tailWord_7355708
  simp only [CollatzResearch.WordTrace]
  refine ⟨134142355617766822877973889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178856474157022430503965185 134142355617766822877973889)
  ·
    refine ⟨100606766713325117158480417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134142355617766822877973889 100606766713325117158480417)
    ·
      refine ⟨75455075034993837868860313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100606766713325117158480417 75455075034993837868860313)
      ·
        refine ⟨56591306276245378401645235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75455075034993837868860313 56591306276245378401645235)
        ·
          refine ⟨84886959414368067602467853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56591306276245378401645235 84886959414368067602467853)
          ·
            refine ⟨31832609780388025350925445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84886959414368067602467853 31832609780388025350925445)
            ·
              refine ⟨5968614333822754753298521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31832609780388025350925445 5968614333822754753298521)
              ·
                refine ⟨4476460750367066064973891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5968614333822754753298521 4476460750367066064973891)
                ·
                  refine ⟨6714691125550599097460837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476460750367066064973891 6714691125550599097460837)
                  ·
                    refine ⟨1259004586040737330773907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6714691125550599097460837 1259004586040737330773907)
                    ·
                      rfl

theorem cell23_7355708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_7355708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355708 prefixEnd_7355708 := by exact prefixLift 7355708
  have htrace : WordTrace (prefixWord ++ tailWord_7355708) baseStart_7355708 baseEnd_7355708 := by
    simpa [prefixWord, tailWord_7355708, baseEnd_7355708] using wordTrace_append hprefix tailTrace_7355708
  have hstable : (prefixWord ++ tailWord_7355708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355708).length < 2 ^ (prefixWord ++ tailWord_7355708).sum := by decide
  have hdescent : baseEnd_7355708 < baseStart_7355708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355748 : List Nat := [2, 3, 1, 1, 3, 2, 1, 5, 1, 1, 3]
def baseStart_7355748 : Nat := 118140960795 + 7355748 * 2 ^ 59
def prefixEnd_7355748 : Nat := 4983230072969 + 3 ^ 40 * 7355748 * 2
def baseEnd_7355748 : Nat := 3777034297348391835821537

theorem tailTrace_7355748 : CollatzResearch.WordTrace tailWord_7355748 prefixEnd_7355748 3777034297348391835821537 := by
  unfold tailWord_7355748
  simp only [CollatzResearch.WordTrace]
  refine ⟨134143085077694366293701949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178857446770259155058269265 134143085077694366293701949)
  ·
    refine ⟨50303656904135387360138231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134143085077694366293701949 50303656904135387360138231)
    ·
      refine ⟨75455485356203081040207347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50303656904135387360138231 75455485356203081040207347)
      ·
        refine ⟨113183228034304621560311021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75455485356203081040207347 113183228034304621560311021)
        ·
          refine ⟨42443710512864233085116633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113183228034304621560311021 42443710512864233085116633)
          ·
            refine ⟨31832782884648174813837475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42443710512864233085116633 31832782884648174813837475)
            ·
              refine ⟨47749174326972262220756213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31832782884648174813837475 47749174326972262220756213)
              ·
                refine ⟨4476485093153649583195895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47749174326972262220756213 4476485093153649583195895)
                ·
                  refine ⟨6714727639730474374793843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476485093153649583195895 6714727639730474374793843)
                  ·
                    refine ⟨10072091459595711562190765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6714727639730474374793843 10072091459595711562190765)
                    ·
                      refine ⟨3777034297348391835821537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10072091459595711562190765 3777034297348391835821537)
                      ·
                        rfl

theorem cell23_7355748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_7355748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355748 prefixEnd_7355748 := by exact prefixLift 7355748
  have htrace : WordTrace (prefixWord ++ tailWord_7355748) baseStart_7355748 baseEnd_7355748 := by
    simpa [prefixWord, tailWord_7355748, baseEnd_7355748] using wordTrace_append hprefix tailTrace_7355748
  have hstable : (prefixWord ++ tailWord_7355748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355748).length < 2 ^ (prefixWord ++ tailWord_7355748).sum := by decide
  have hdescent : baseEnd_7355748 < baseStart_7355748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355751 : List Nat := [1, 1, 5, 1, 4, 1, 1, 3, 1, 5]
def baseStart_7355751 : Nat := 118140960795 + 7355751 * 2 ^ 59
def prefixEnd_7355751 : Nat := 4983230072969 + 3 ^ 40 * 7355751 * 2
def baseEnd_7355751 : Nat := 1259011945930118441361341

theorem tailTrace_7355751 : CollatzResearch.WordTrace tailWord_7355751 prefixEnd_7355751 1259011945930118441361341 := by
  unfold tailWord_7355751
  simp only [CollatzResearch.WordTrace]
  refine ⟨268286279574377864099763107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178857519716251909399842071 268286279574377864099763107)
  ·
    refine ⟨402429419361566796149644661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268286279574377864099763107 402429419361566796149644661)
    ·
      refine ⟨37727758065146887139029187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 402429419361566796149644661 37727758065146887139029187)
      ·
        refine ⟨56591637097720330708543781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37727758065146887139029187 56591637097720330708543781)
        ·
          refine ⟨10610931955822562007851959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56591637097720330708543781 10610931955822562007851959)
          ·
            refine ⟨15916397933733843011777939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10610931955822562007851959 15916397933733843011777939)
            ·
              refine ⟨23874596900600764517666909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15916397933733843011777939 23874596900600764517666909)
              ·
                refine ⟨8952973837725286694125091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23874596900600764517666909 8952973837725286694125091)
                ·
                  refine ⟨13429460756587930041187637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8952973837725286694125091 13429460756587930041187637)
                  ·
                    refine ⟨1259011945930118441361341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13429460756587930041187637 1259011945930118441361341)
                    ·
                      rfl

theorem cell23_7355751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_7355751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355751 prefixEnd_7355751 := by exact prefixLift 7355751
  have htrace : WordTrace (prefixWord ++ tailWord_7355751) baseStart_7355751 baseEnd_7355751 := by
    simpa [prefixWord, tailWord_7355751, baseEnd_7355751] using wordTrace_append hprefix tailTrace_7355751
  have hstable : (prefixWord ++ tailWord_7355751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355751).length < 2 ^ (prefixWord ++ tailWord_7355751).sum := by decide
  have hdescent : baseEnd_7355751 < baseStart_7355751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355767 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_7355767 : Nat := 118140960795 + 7355767 * 2 ^ 59
def prefixEnd_7355767 : Nat := 4983230072969 + 3 ^ 40 * 7355767 * 2
def baseEnd_7355767 : Nat := 3777044053480827261483949

theorem tailTrace_7355767 : CollatzResearch.WordTrace tailWord_7355767 prefixEnd_7355767 3777044053480827261483949 := by
  unfold tailWord_7355767
  simp only [CollatzResearch.WordTrace]
  refine ⟨268286863142319898832345555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178857908761546599221563703 268286863142319898832345555)
  ·
    refine ⟨402430294713479848248518333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268286863142319898832345555 402430294713479848248518333)
    ·
      refine ⟨150911360517554943093194375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402430294713479848248518333 150911360517554943093194375)
      ·
        refine ⟨226367040776332414639791563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150911360517554943093194375 226367040776332414639791563)
        ·
          refine ⟨339550561164498621959687345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226367040776332414639791563 339550561164498621959687345)
          ·
            refine ⟨254662920873373966469765509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339550561164498621959687345 254662920873373966469765509)
            ·
              refine ⟨47749297663757618713081033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254662920873373966469765509 47749297663757618713081033)
              ·
                refine ⟨35811973247818214034810775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47749297663757618713081033 35811973247818214034810775)
                ·
                  refine ⟨53717959871727321052216163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35811973247818214034810775 53717959871727321052216163)
                  ·
                    refine ⟨80576939807590981578324245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53717959871727321052216163 80576939807590981578324245)
                    ·
                      refine ⟨3777044053480827261483949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80576939807590981578324245 3777044053480827261483949)
                      ·
                        rfl

theorem cell23_7355767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_7355767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355767 prefixEnd_7355767 := by exact prefixLift 7355767
  have htrace : WordTrace (prefixWord ++ tailWord_7355767) baseStart_7355767 baseEnd_7355767 := by
    simpa [prefixWord, tailWord_7355767, baseEnd_7355767] using wordTrace_append hprefix tailTrace_7355767
  have hstable : (prefixWord ++ tailWord_7355767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355767).length < 2 ^ (prefixWord ++ tailWord_7355767).sum := by decide
  have hdescent : baseEnd_7355767 < baseStart_7355767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355784 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_7355784 : Nat := 118140960795 + 7355784 * 2 ^ 59
def prefixEnd_7355784 : Nat := 4983230072969 + 3 ^ 40 * 7355784 * 2
def baseEnd_7355784 : Nat := 3777052782651953694971371

theorem tailTrace_7355784 : CollatzResearch.WordTrace tailWord_7355784 prefixEnd_7355784 3777052782651953694971371 := by
  unfold tailWord_7355784
  simp only [CollatzResearch.WordTrace]
  refine ⟨134143741591629155367857203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178858322122172207157142937 134143741591629155367857203)
  ·
    refine ⟨201215612387443733051785805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134143741591629155367857203 201215612387443733051785805)
    ·
      refine ⟨75455854645291399894419677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201215612387443733051785805 75455854645291399894419677)
      ·
        refine ⟨28295945491984274960407379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75455854645291399894419677 28295945491984274960407379)
        ·
          refine ⟨42443918237976412440611069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28295945491984274960407379 42443918237976412440611069)
          ·
            refine ⟨15916469339241154665229151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42443918237976412440611069 15916469339241154665229151)
            ·
              refine ⟨23874704008861731997843727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15916469339241154665229151 23874704008861731997843727)
              ·
                refine ⟨35812056013292597996765591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23874704008861731997843727 35812056013292597996765591)
                ·
                  refine ⟨53718084019938896995148387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35812056013292597996765591 53718084019938896995148387)
                  ·
                    refine ⟨80577126029908345492722581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53718084019938896995148387 80577126029908345492722581)
                    ·
                      refine ⟨3777052782651953694971371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80577126029908345492722581 3777052782651953694971371)
                      ·
                        rfl

theorem cell23_7355784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_7355784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355784 prefixEnd_7355784 := by exact prefixLift 7355784
  have htrace : WordTrace (prefixWord ++ tailWord_7355784) baseStart_7355784 baseEnd_7355784 := by
    simpa [prefixWord, tailWord_7355784, baseEnd_7355784] using wordTrace_append hprefix tailTrace_7355784
  have hstable : (prefixWord ++ tailWord_7355784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355784).length < 2 ^ (prefixWord ++ tailWord_7355784).sum := by decide
  have hdescent : baseEnd_7355784 < baseStart_7355784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355831 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 3, 3, 2]
def baseStart_7355831 : Nat := 118140960795 + 7355831 * 2 ^ 59
def prefixEnd_7355831 : Nat := 4983230072969 + 3 ^ 40 * 7355831 * 2
def baseEnd_7355831 : Nat := 3777076916242715011083655

theorem tailTrace_7355831 : CollatzResearch.WordTrace tailWord_7355831 prefixEnd_7355831 3777076916242715011083655 := by
  unfold tailWord_7355831
  simp only [CollatzResearch.WordTrace]
  refine ⟨268289197414088037762675347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178859464942725358508450231 268289197414088037762675347)
  ·
    refine ⟨402433796121132056644013021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268289197414088037762675347 402433796121132056644013021)
    ·
      refine ⟨150912673545424521241504883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402433796121132056644013021 150912673545424521241504883)
      ·
        refine ⟨226369010318136781862257325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150912673545424521241504883 226369010318136781862257325)
        ·
          refine ⟨84888378869301293198346497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226369010318136781862257325 84888378869301293198346497)
          ·
            refine ⟨63666284151975969898759873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84888378869301293198346497 63666284151975969898759873)
            ·
              refine ⟨47749713113981977424069905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63666284151975969898759873 47749713113981977424069905)
              ·
                refine ⟨35812284835486483068052429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47749713113981977424069905 35812284835486483068052429)
                ·
                  refine ⟨13429606813307431150519661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35812284835486483068052429 13429606813307431150519661)
                  ·
                    refine ⟨5036102554990286681444873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13429606813307431150519661 5036102554990286681444873)
                    ·
                      refine ⟨3777076916242715011083655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5036102554990286681444873 3777076916242715011083655)
                      ·
                        rfl

theorem cell23_7355831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 3, 2].length) (baseStart_7355831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355831 prefixEnd_7355831 := by exact prefixLift 7355831
  have htrace : WordTrace (prefixWord ++ tailWord_7355831) baseStart_7355831 baseEnd_7355831 := by
    simpa [prefixWord, tailWord_7355831, baseEnd_7355831] using wordTrace_append hprefix tailTrace_7355831
  have hstable : (prefixWord ++ tailWord_7355831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355831).length < 2 ^ (prefixWord ++ tailWord_7355831).sum := by decide
  have hdescent : baseEnd_7355831 < baseStart_7355831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355864 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_7355864 : Nat := 118140960795 + 7355864 * 2 ^ 59
def prefixEnd_7355864 : Nat := 4983230072969 + 3 ^ 40 * 7355864 * 2
def baseEnd_7355864 : Nat := 3777093861104313381971003

theorem tailTrace_7355864 : CollatzResearch.WordTrace tailWord_7355864 prefixEnd_7355864 3777093861104313381971003 := by
  unfold tailWord_7355864
  simp only [CollatzResearch.WordTrace]
  refine ⟨134145200511484242199313323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178860267348645656265751097 134145200511484242199313323)
  ·
    refine ⟨201217800767226363298969985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134145200511484242199313323 201217800767226363298969985)
    ·
      refine ⟨150913350575419772474227489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201217800767226363298969985 150913350575419772474227489)
      ·
        refine ⟨113185012931564829355670617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150913350575419772474227489 113185012931564829355670617)
        ·
          refine ⟨84888759698673622016752963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113185012931564829355670617 84888759698673622016752963)
          ·
            refine ⟨127333139548010433025129445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84888759698673622016752963 127333139548010433025129445)
            ·
              refine ⟨23874963665251956192211771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127333139548010433025129445 23874963665251956192211771)
              ·
                refine ⟨35812445497877934288317657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23874963665251956192211771 35812445497877934288317657)
                ·
                  refine ⟨26859334123408450716238243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35812445497877934288317657 26859334123408450716238243)
                  ·
                    refine ⟨40289001185112676074357365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26859334123408450716238243 40289001185112676074357365)
                    ·
                      refine ⟨3777093861104313381971003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40289001185112676074357365 3777093861104313381971003)
                      ·
                        rfl

theorem cell23_7355864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_7355864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355864 prefixEnd_7355864 := by exact prefixLift 7355864
  have htrace : WordTrace (prefixWord ++ tailWord_7355864) baseStart_7355864 baseEnd_7355864 := by
    simpa [prefixWord, tailWord_7355864, baseEnd_7355864] using wordTrace_append hprefix tailTrace_7355864
  have hstable : (prefixWord ++ tailWord_7355864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355864).length < 2 ^ (prefixWord ++ tailWord_7355864).sum := by decide
  have hdescent : baseEnd_7355864 < baseStart_7355864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355865 : List Nat := [1, 2, 1, 2, 4, 3, 3, 1, 1, 3, 2]
def baseStart_7355865 : Nat := 118140960795 + 7355865 * 2 ^ 59
def prefixEnd_7355865 : Nat := 4983230072969 + 3 ^ 40 * 7355865 * 2
def baseEnd_7355865 : Nat := 3777094374584967878058499

theorem tailTrace_7355865 : CollatzResearch.WordTrace tailWord_7355865 prefixEnd_7355865 3777094374584967878058499 := by
  unfold tailWord_7355865
  simp only [CollatzResearch.WordTrace]
  refine ⟨268290437495964861569413049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178860291663976574379608699 268290437495964861569413049)
  ·
    refine ⟨201217828121973646177059787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268290437495964861569413049 201217828121973646177059787)
    ·
      refine ⟨301826742182960469265589681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201217828121973646177059787 301826742182960469265589681)
      ·
        refine ⟨226370056637220351949192261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301826742182960469265589681 226370056637220351949192261)
        ·
          refine ⟨42444385619478815990473549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226370056637220351949192261 42444385619478815990473549)
          ·
            refine ⟨15916644607304555996427581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42444385619478815990473549 15916644607304555996427581)
            ·
              refine ⟨5968741727739208498660343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15916644607304555996427581 5968741727739208498660343)
              ·
                refine ⟨8953112591608812747990515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5968741727739208498660343 8953112591608812747990515)
                ·
                  refine ⟨13429668887413219121985773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8953112591608812747990515 13429668887413219121985773)
                  ·
                    refine ⟨5036125832779957170744665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13429668887413219121985773 5036125832779957170744665)
                    ·
                      refine ⟨3777094374584967878058499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5036125832779957170744665 3777094374584967878058499)
                      ·
                        rfl

theorem cell23_7355865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 1, 3, 2].length) (baseStart_7355865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355865 prefixEnd_7355865 := by exact prefixLift 7355865
  have htrace : WordTrace (prefixWord ++ tailWord_7355865) baseStart_7355865 baseEnd_7355865 := by
    simpa [prefixWord, tailWord_7355865, baseEnd_7355865] using wordTrace_append hprefix tailTrace_7355865
  have hstable : (prefixWord ++ tailWord_7355865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355865).length < 2 ^ (prefixWord ++ tailWord_7355865).sum := by decide
  have hdescent : baseEnd_7355865 < baseStart_7355865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355988 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_7355988 : Nat := 118140960795 + 7355988 * 2 ^ 59
def prefixEnd_7355988 : Nat := 4983230072969 + 3 ^ 40 * 7355988 * 2
def baseEnd_7355988 : Nat := 3777157532705470896820433

theorem tailTrace_7355988 : CollatzResearch.WordTrace tailWord_7355988 prefixEnd_7355988 3777157532705470896820433 := by
  unfold tailWord_7355988
  simp only [CollatzResearch.WordTrace]
  refine ⟨134147461837259626788070309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178863282449679502384093745 134147461837259626788070309)
  ·
    refine ⟨25152649094486180022763183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134147461837259626788070309 25152649094486180022763183)
    ·
      refine ⟨37728973641729270034144775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25152649094486180022763183 37728973641729270034144775)
      ·
        refine ⟨56593460462593905051217163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37728973641729270034144775 56593460462593905051217163)
        ·
          refine ⟨84890190693890857576825745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56593460462593905051217163 84890190693890857576825745)
          ·
            refine ⟨63667643020418143182619309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84890190693890857576825745 63667643020418143182619309)
            ·
              refine ⟨23875366132656803693482241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63667643020418143182619309 23875366132656803693482241)
              ·
                refine ⟨17906524599492602770111681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23875366132656803693482241 17906524599492602770111681)
                ·
                  refine ⟨13429893449619452077583761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17906524599492602770111681 13429893449619452077583761)
                  ·
                    refine ⟨10072420087214589058187821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13429893449619452077583761 10072420087214589058187821)
                    ·
                      refine ⟨3777157532705470896820433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10072420087214589058187821 3777157532705470896820433)
                      ·
                        rfl

theorem cell23_7355988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_7355988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355988 prefixEnd_7355988 := by exact prefixLift 7355988
  have htrace : WordTrace (prefixWord ++ tailWord_7355988) baseStart_7355988 baseEnd_7355988 := by
    simpa [prefixWord, tailWord_7355988, baseEnd_7355988] using wordTrace_append hprefix tailTrace_7355988
  have hstable : (prefixWord ++ tailWord_7355988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355988).length < 2 ^ (prefixWord ++ tailWord_7355988).sum := by decide
  have hdescent : baseEnd_7355988 < baseStart_7355988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7355994 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_7355994 : Nat := 118140960795 + 7355994 * 2 ^ 59
def prefixEnd_7355994 : Nat := 4983230072969 + 3 ^ 40 * 7355994 * 2
def baseEnd_7355994 : Nat := 3777160613589397873345405

theorem tailTrace_7355994 : CollatzResearch.WordTrace tailWord_7355994 prefixEnd_7355994 3777160613589397873345405 := by
  unfold tailWord_7355994
  simp only [CollatzResearch.WordTrace]
  refine ⟨67073785628124379150214759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178863428341665011067239357 67073785628124379150214759)
  ·
    refine ⟨100610678442186568725322139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67073785628124379150214759 100610678442186568725322139)
    ·
      refine ⟨150916017663279853087983209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100610678442186568725322139 150916017663279853087983209)
      ·
        refine ⟨113187013247459889815987407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150916017663279853087983209 113187013247459889815987407)
        ·
          refine ⟨169780519871189834723981111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113187013247459889815987407 169780519871189834723981111)
          ·
            refine ⟨254670779806784752085971667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169780519871189834723981111 254670779806784752085971667)
            ·
              refine ⟨382006169710177128128957501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254670779806784752085971667 382006169710177128128957501)
              ·
                refine ⟨143252313641316423048359063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382006169710177128128957501 143252313641316423048359063)
                ·
                  refine ⟨214878470461974634572538595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143252313641316423048359063 214878470461974634572538595)
                  ·
                    refine ⟨322317705692961951858807893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 214878470461974634572538595 322317705692961951858807893)
                    ·
                      refine ⟨3777160613589397873345405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 322317705692961951858807893 3777160613589397873345405)
                      ·
                        rfl

theorem cell23_7355994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_7355994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7355994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7355994 prefixEnd_7355994 := by exact prefixLift 7355994
  have htrace : WordTrace (prefixWord ++ tailWord_7355994) baseStart_7355994 baseEnd_7355994 := by
    simpa [prefixWord, tailWord_7355994, baseEnd_7355994] using wordTrace_append hprefix tailTrace_7355994
  have hstable : (prefixWord ++ tailWord_7355994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7355994).length < 2 ^ (prefixWord ++ tailWord_7355994).sum := by decide
  have hdescent : baseEnd_7355994 < baseStart_7355994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7355994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356008 : List Nat := [2, 1, 4, 3, 1, 2, 1, 3, 6]
def baseStart_7356008 : Nat := 118140960795 + 7356008 * 2 ^ 59
def prefixEnd_7356008 : Nat := 4983230072969 + 3 ^ 40 * 7356008 * 2
def baseEnd_7356008 : Nat := 419685311368728979841149

theorem tailTrace_7356008 : CollatzResearch.WordTrace tailWord_7356008 prefixEnd_7356008 419685311368728979841149 := by
  unfold tailWord_7356008
  simp only [CollatzResearch.WordTrace]
  refine ⟨134147826567223398495934339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178863768756297864661245785 134147826567223398495934339)
  ·
    refine ⟨201221739850835097743901509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134147826567223398495934339 201221739850835097743901509)
    ·
      refine ⟨37729076222031580826981533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201221739850835097743901509 37729076222031580826981533)
      ·
        refine ⟨14148403583261842810118075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37729076222031580826981533 14148403583261842810118075)
        ·
          refine ⟨21222605374892764215177113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14148403583261842810118075 21222605374892764215177113)
          ·
            refine ⟨15916954031169573161382835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21222605374892764215177113 15916954031169573161382835)
            ·
              refine ⟨23875431046754359742074253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15916954031169573161382835 23875431046754359742074253)
              ·
                refine ⟨8953286642532884903277845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23875431046754359742074253 8953286642532884903277845)
                ·
                  refine ⟨419685311368728979841149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8953286642532884903277845 419685311368728979841149)
                  ·
                    rfl

theorem cell23_7356008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 6].length) (baseStart_7356008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356008 prefixEnd_7356008 := by exact prefixLift 7356008
  have htrace : WordTrace (prefixWord ++ tailWord_7356008) baseStart_7356008 baseEnd_7356008 := by
    simpa [prefixWord, tailWord_7356008, baseEnd_7356008] using wordTrace_append hprefix tailTrace_7356008
  have hstable : (prefixWord ++ tailWord_7356008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356008).length < 2 ^ (prefixWord ++ tailWord_7356008).sum := by decide
  have hdescent : baseEnd_7356008 < baseStart_7356008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356035 : List Nat := [1, 1, 1, 3, 3, 1, 1, 7, 1, 1, 3]
def baseStart_7356035 : Nat := 118140960795 + 7356035 * 2 ^ 59
def prefixEnd_7356035 : Nat := 4983230072969 + 3 ^ 40 * 7356035 * 2
def baseEnd_7356035 : Nat := 3777181666296232212932717

theorem tailTrace_7356035 : CollatzResearch.WordTrace tailWord_7356035 prefixEnd_7356035 3777181666296232212932717 := by
  unfold tailWord_7356035
  simp only [CollatzResearch.WordTrace]
  refine ⟨268296637905348980603101559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178864425270232653735401039 268296637905348980603101559)
  ·
    refine ⟨402444956858023470904652339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268296637905348980603101559 402444956858023470904652339)
    ·
      refine ⟨603667435287035206356978509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402444956858023470904652339 603667435287035206356978509)
      ·
        refine ⟨226375288232638202383866941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 603667435287035206356978509 226375288232638202383866941)
        ·
          refine ⟨84890733087239325893950103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226375288232638202383866941 84890733087239325893950103)
          ·
            refine ⟨127336099630858988840925155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84890733087239325893950103 127336099630858988840925155)
            ·
              refine ⟨191004149446288483261387733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127336099630858988840925155 191004149446288483261387733)
              ·
                refine ⟨4476659752647386326438775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 191004149446288483261387733 4476659752647386326438775)
                ·
                  refine ⟨6714989628971079489658163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476659752647386326438775 6714989628971079489658163)
                  ·
                    refine ⟨10072484443456619234487245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6714989628971079489658163 10072484443456619234487245)
                    ·
                      refine ⟨3777181666296232212932717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10072484443456619234487245 3777181666296232212932717)
                      ·
                        rfl

theorem cell23_7356035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 1, 1, 3].length) (baseStart_7356035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356035 prefixEnd_7356035 := by exact prefixLift 7356035
  have htrace : WordTrace (prefixWord ++ tailWord_7356035) baseStart_7356035 baseEnd_7356035 := by
    simpa [prefixWord, tailWord_7356035, baseEnd_7356035] using wordTrace_append hprefix tailTrace_7356035
  have hstable : (prefixWord ++ tailWord_7356035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356035).length < 2 ^ (prefixWord ++ tailWord_7356035).sum := by decide
  have hdescent : baseEnd_7356035 < baseStart_7356035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356061 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_7356061 : Nat := 118140960795 + 7356061 * 2 ^ 59
def prefixEnd_7356061 : Nat := 4983230072969 + 3 ^ 40 * 7356061 * 2
def baseEnd_7356061 : Nat := 3777195016793249111207597

theorem tailTrace_7356061 : CollatzResearch.WordTrace tailWord_7356061 prefixEnd_7356061 3777195016793249111207597 := by
  unfold tailWord_7356061
  simp only [CollatzResearch.WordTrace]
  refine ⟨268297586203254787043548037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178865057468836524695698691 268297586203254787043548037)
  ·
    refine ⟨50305797413110272570665257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268297586203254787043548037 50305797413110272570665257)
    ·
      refine ⟨37729348059832704427998943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50305797413110272570665257 37729348059832704427998943)
      ·
        refine ⟨56594022089749056641998415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37729348059832704427998943 56594022089749056641998415)
        ·
          refine ⟨84891033134623584962997623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56594022089749056641998415 84891033134623584962997623)
          ·
            refine ⟨127336549701935377444496435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84891033134623584962997623 127336549701935377444496435)
            ·
              refine ⟨191004824552903066166744653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127336549701935377444496435 191004824552903066166744653)
              ·
                refine ⟨71626809207338649812529245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191004824552903066166744653 71626809207338649812529245)
                ·
                  refine ⟨26860053452751993679698467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71626809207338649812529245 26860053452751993679698467)
                  ·
                    refine ⟨40290080179127990519547701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26860053452751993679698467 40290080179127990519547701)
                    ·
                      refine ⟨3777195016793249111207597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40290080179127990519547701 3777195016793249111207597)
                      ·
                        rfl

theorem cell23_7356061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_7356061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356061 prefixEnd_7356061 := by exact prefixLift 7356061
  have htrace : WordTrace (prefixWord ++ tailWord_7356061) baseStart_7356061 baseEnd_7356061 := by
    simpa [prefixWord, tailWord_7356061, baseEnd_7356061] using wordTrace_append hprefix tailTrace_7356061
  have hstable : (prefixWord ++ tailWord_7356061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356061).length < 2 ^ (prefixWord ++ tailWord_7356061).sum := by decide
  have hdescent : baseEnd_7356061 < baseStart_7356061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356068 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_7356068 : Nat := 118140960795 + 7356068 * 2 ^ 59
def prefixEnd_7356068 : Nat := 4983230072969 + 3 ^ 40 * 7356068 * 2
def baseEnd_7356068 : Nat := 1259066203719276861273355

theorem tailTrace_7356068 : CollatzResearch.WordTrace tailWord_7356068 prefixEnd_7356068 1259066203719276861273355 := by
  unfold tailWord_7356068
  simp only [CollatzResearch.WordTrace]
  refine ⟨134148920757114713619526429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178865227676152951492701905 134148920757114713619526429)
  ·
    refine ⟨50305845283918017607322411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134148920757114713619526429 50305845283918017607322411)
    ·
      refine ⟨75458767925877026410983617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50305845283918017607322411 75458767925877026410983617)
      ·
        refine ⟨56594075944407769808237713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75458767925877026410983617 56594075944407769808237713)
        ·
          refine ⟨42445556958305827356178285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56594075944407769808237713 42445556958305827356178285)
          ·
            refine ⟨15917083859364685258566857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42445556958305827356178285 15917083859364685258566857)
            ·
              refine ⟨11937812894523513943925143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15917083859364685258566857 11937812894523513943925143)
              ·
                refine ⟨17906719341785270915887715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11937812894523513943925143 17906719341785270915887715)
                ·
                  refine ⟨26860079012677906373831573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17906719341785270915887715 26860079012677906373831573)
                  ·
                    refine ⟨1259066203719276861273355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26860079012677906373831573 1259066203719276861273355)
                    ·
                      rfl

theorem cell23_7356068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_7356068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356068 prefixEnd_7356068 := by exact prefixLift 7356068
  have htrace : WordTrace (prefixWord ++ tailWord_7356068) baseStart_7356068 baseEnd_7356068 := by
    simpa [prefixWord, tailWord_7356068, baseEnd_7356068] using wordTrace_append hprefix tailTrace_7356068
  have hstable : (prefixWord ++ tailWord_7356068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356068).length < 2 ^ (prefixWord ++ tailWord_7356068).sum := by decide
  have hdescent : baseEnd_7356068 < baseStart_7356068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356086 : List Nat := [5, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_7356086 : Nat := 118140960795 + 7356086 * 2 ^ 59
def prefixEnd_7356086 : Nat := 4983230072969 + 3 ^ 40 * 7356086 * 2
def baseEnd_7356086 : Nat := 3777207853809611513394983

theorem tailTrace_7356086 : CollatzResearch.WordTrace tailWord_7356086 prefixEnd_7356086 3777207853809611513394983 := by
  unfold tailWord_7356086
  simp only [CollatzResearch.WordTrace]
  refine ⟨16768656126760263519575507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178865665352109477542138741 16768656126760263519575507)
  ·
    refine ⟨25152984190140395279363261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16768656126760263519575507 25152984190140395279363261)
    ·
      refine ⟨9432369071302648229761223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25152984190140395279363261 9432369071302648229761223)
      ·
        refine ⟨14148553606953972344641835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9432369071302648229761223 14148553606953972344641835)
        ·
          refine ⟨21222830410430958516962753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14148553606953972344641835 21222830410430958516962753)
          ·
            refine ⟨15917122807823218887722065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21222830410430958516962753 15917122807823218887722065)
            ·
              refine ⟨11937842105867414165791549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15917122807823218887722065 11937842105867414165791549)
              ·
                refine ⟨4476690789700280312171831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11937842105867414165791549 4476690789700280312171831)
                ·
                  refine ⟨6715036184550420468257747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476690789700280312171831 6715036184550420468257747)
                  ·
                    refine ⟨10072554276825630702386621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6715036184550420468257747 10072554276825630702386621)
                    ·
                      refine ⟨3777207853809611513394983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10072554276825630702386621 3777207853809611513394983)
                      ·
                        rfl

theorem cell23_7356086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_7356086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356086 prefixEnd_7356086 := by exact prefixLift 7356086
  have htrace : WordTrace (prefixWord ++ tailWord_7356086) baseStart_7356086 baseEnd_7356086 := by
    simpa [prefixWord, tailWord_7356086, baseEnd_7356086] using wordTrace_append hprefix tailTrace_7356086
  have hstable : (prefixWord ++ tailWord_7356086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356086).length < 2 ^ (prefixWord ++ tailWord_7356086).sum := by decide
  have hdescent : baseEnd_7356086 < baseStart_7356086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356092 : List Nat := [2, 2, 2, 3, 1, 4, 2, 1, 1, 1, 4]
def baseStart_7356092 : Nat := 118140960795 + 7356092 * 2 ^ 59
def prefixEnd_7356092 : Nat := 4983230072969 + 3 ^ 40 * 7356092 * 2
def baseEnd_7356092 : Nat := 3777210934693538489919955

theorem tailTrace_7356092 : CollatzResearch.WordTrace tailWord_7356092 prefixEnd_7356092 3777210934693538489919955 := by
  unfold tailWord_7356092
  simp only [CollatzResearch.WordTrace]
  refine ⟨134149358433071239668963265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178865811244094986225284353 134149358433071239668963265)
  ·
    refine ⟨100612018824803429751722449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134149358433071239668963265 100612018824803429751722449)
    ·
      refine ⟨75459014118602572313791837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100612018824803429751722449 75459014118602572313791837)
      ·
        refine ⟨28297130294475964617671939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75459014118602572313791837 28297130294475964617671939)
        ·
          refine ⟨42445695441713946926507909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28297130294475964617671939 42445695441713946926507909)
          ·
            refine ⟨7958567895321365048720233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42445695441713946926507909 7958567895321365048720233)
            ·
              refine ⟨5968925921491023786540175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7958567895321365048720233 5968925921491023786540175)
              ·
                refine ⟨8953388882236535679810263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5968925921491023786540175 8953388882236535679810263)
                ·
                  refine ⟨13430083323354803519715395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8953388882236535679810263 13430083323354803519715395)
                  ·
                    refine ⟨20145124985032205279573093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13430083323354803519715395 20145124985032205279573093)
                    ·
                      refine ⟨3777210934693538489919955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20145124985032205279573093 3777210934693538489919955)
                      ·
                        rfl

theorem cell23_7356092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_7356092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356092 prefixEnd_7356092 := by exact prefixLift 7356092
  have htrace : WordTrace (prefixWord ++ tailWord_7356092) baseStart_7356092 baseEnd_7356092 := by
    simpa [prefixWord, tailWord_7356092, baseEnd_7356092] using wordTrace_append hprefix tailTrace_7356092
  have hstable : (prefixWord ++ tailWord_7356092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356092).length < 2 ^ (prefixWord ++ tailWord_7356092).sum := by decide
  have hdescent : baseEnd_7356092 < baseStart_7356092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356109 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_7356109 : Nat := 118140960795 + 7356109 * 2 ^ 59
def prefixEnd_7356109 : Nat := 4983230072969 + 3 ^ 40 * 7356109 * 2
def baseEnd_7356109 : Nat := 3777219663864664923407377

theorem tailTrace_7356109 : CollatzResearch.WordTrace tailWord_7356109 prefixEnd_7356109 3777219663864664923407377 := by
  unfold tailWord_7356109
  simp only [CollatzResearch.WordTrace]
  refine ⟨268299336907080891241295381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178866224604720594160863587 268299336907080891241295381)
  ·
    refine ⟨12576531417519416776935721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 268299336907080891241295381 12576531417519416776935721)
    ·
      refine ⟨9432398563139562582701791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12576531417519416776935721 9432398563139562582701791)
      ·
        refine ⟨14148597844709343874052687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9432398563139562582701791 14148597844709343874052687)
        ·
          refine ⟨21222896767064015811079031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14148597844709343874052687 21222896767064015811079031)
          ·
            refine ⟨31834345150596023716618547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21222896767064015811079031 31834345150596023716618547)
            ·
              refine ⟨47751517725894035574927821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31834345150596023716618547 47751517725894035574927821)
              ·
                refine ⟨17906819147210263340597933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47751517725894035574927821 17906819147210263340597933)
                ·
                  refine ⟨6715057180203848752724225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17906819147210263340597933 6715057180203848752724225)
                  ·
                    refine ⟨5036292885152886564543169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6715057180203848752724225 5036292885152886564543169)
                    ·
                      refine ⟨3777219663864664923407377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5036292885152886564543169 3777219663864664923407377)
                      ·
                        rfl

theorem cell23_7356109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_7356109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356109 prefixEnd_7356109 := by exact prefixLift 7356109
  have htrace : WordTrace (prefixWord ++ tailWord_7356109) baseStart_7356109 baseEnd_7356109 := by
    simpa [prefixWord, tailWord_7356109, baseEnd_7356109] using wordTrace_append hprefix tailTrace_7356109
  have hstable : (prefixWord ++ tailWord_7356109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356109).length < 2 ^ (prefixWord ++ tailWord_7356109).sum := by decide
  have hdescent : baseEnd_7356109 < baseStart_7356109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356151 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_7356151 : Nat := 118140960795 + 7356151 * 2 ^ 59
def prefixEnd_7356151 : Nat := 4983230072969 + 3 ^ 40 * 7356151 * 2
def baseEnd_7356151 : Nat := 3777241230052153759082183

theorem tailTrace_7356151 : CollatzResearch.WordTrace tailWord_7356151 prefixEnd_7356151 3777241230052153759082183 := by
  unfold tailWord_7356151
  simp only [CollatzResearch.WordTrace]
  refine ⟨268300868772928732414324307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178867245848619154942882871 268300868772928732414324307)
  ·
    refine ⟨402451303159393098621486461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268300868772928732414324307 402451303159393098621486461)
    ·
      refine ⟨150919238684772411983057423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402451303159393098621486461 150919238684772411983057423)
      ·
        refine ⟨226378858027158617974586135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150919238684772411983057423 226378858027158617974586135)
        ·
          refine ⟨339568287040737926961879203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226378858027158617974586135 339568287040737926961879203)
          ·
            refine ⟨509352430561106890442818805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339568287040737926961879203 509352430561106890442818805)
            ·
              refine ⟨47751790365103770979014263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 509352430561106890442818805 47751790365103770979014263)
              ·
                refine ⟨71627685547655656468521395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47751790365103770979014263 71627685547655656468521395)
                ·
                  refine ⟨107441528321483484702782093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71627685547655656468521395 107441528321483484702782093)
                  ·
                    refine ⟨40290573120556306763543285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107441528321483484702782093 40290573120556306763543285)
                    ·
                      refine ⟨3777241230052153759082183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40290573120556306763543285 3777241230052153759082183)
                      ·
                        rfl

theorem cell23_7356151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_7356151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356151 prefixEnd_7356151 := by exact prefixLift 7356151
  have htrace : WordTrace (prefixWord ++ tailWord_7356151) baseStart_7356151 baseEnd_7356151 := by
    simpa [prefixWord, tailWord_7356151, baseEnd_7356151] using wordTrace_append hprefix tailTrace_7356151
  have hstable : (prefixWord ++ tailWord_7356151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356151).length < 2 ^ (prefixWord ++ tailWord_7356151).sum := by decide
  have hdescent : baseEnd_7356151 < baseStart_7356151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356166 : List Nat := [6, 2, 2, 1, 1, 1, 2, 8]
def baseStart_7356166 : Nat := 118140960795 + 7356166 * 2 ^ 59
def prefixEnd_7356166 : Nat := 4983230072969 + 3 ^ 40 * 7356166 * 2
def baseEnd_7356166 : Nat := 139898108602295229644245

theorem tailTrace_7356166 : CollatzResearch.WordTrace tailWord_7356166 prefixEnd_7356166 139898108602295229644245 := by
  unfold tailWord_7356166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8384419245871074686753761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178867610578582926650746901 8384419245871074686753761)
  ·
    refine ⟨6288314434403306015065321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8384419245871074686753761 6288314434403306015065321)
    ·
      refine ⟨4716235825802479511298991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6288314434403306015065321 4716235825802479511298991)
      ·
        refine ⟨7074353738703719266948487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4716235825802479511298991 7074353738703719266948487)
        ·
          refine ⟨10611530608055578900422731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7074353738703719266948487 10611530608055578900422731)
          ·
            refine ⟨15917295912083368350634097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10611530608055578900422731 15917295912083368350634097)
            ·
              refine ⟨11937971934062526262975573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15917295912083368350634097 11937971934062526262975573)
              ·
                refine ⟨139898108602295229644245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11937971934062526262975573 139898108602295229644245)
                ·
                  rfl

theorem cell23_7356166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_7356166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356166 prefixEnd_7356166 := by exact prefixLift 7356166
  have htrace : WordTrace (prefixWord ++ tailWord_7356166) baseStart_7356166 baseEnd_7356166 := by
    simpa [prefixWord, tailWord_7356166, baseEnd_7356166] using wordTrace_append hprefix tailTrace_7356166
  have hstable : (prefixWord ++ tailWord_7356166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356166).length < 2 ^ (prefixWord ++ tailWord_7356166).sum := by decide
  have hdescent : baseEnd_7356166 < baseStart_7356166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356168 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_7356168 : Nat := 118140960795 + 7356168 * 2 ^ 59
def prefixEnd_7356168 : Nat := 4983230072969 + 3 ^ 40 * 7356168 * 2
def baseEnd_7356168 : Nat := 3777249959223280192569605

theorem tailTrace_7356168 : CollatzResearch.WordTrace tailWord_7356168 prefixEnd_7356168 3777249959223280192569605 := by
  unfold tailWord_7356168
  simp only [CollatzResearch.WordTrace]
  refine ⟨134150744406933572158846579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178867659209244762878462105 134150744406933572158846579)
  ·
    refine ⟨201226116610400358238269869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134150744406933572158846579 201226116610400358238269869)
    ·
      refine ⟨75459793728900134339351201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201226116610400358238269869 75459793728900134339351201)
      ·
        refine ⟨56594845296675100754513401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75459793728900134339351201 56594845296675100754513401)
        ·
          refine ⟨42446133972506325565885051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56594845296675100754513401 42446133972506325565885051)
          ·
            refine ⟨63669200958759488348827577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42446133972506325565885051 63669200958759488348827577)
            ·
              refine ⟨47751900719069616261620683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63669200958759488348827577 47751900719069616261620683)
              ·
                refine ⟨71627851078604424392431025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47751900719069616261620683 71627851078604424392431025)
                ·
                  refine ⟨53720888308953318294323269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71627851078604424392431025 53720888308953318294323269)
                  ·
                    refine ⟨10072666557928747180185613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53720888308953318294323269 10072666557928747180185613)
                    ·
                      refine ⟨3777249959223280192569605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10072666557928747180185613 3777249959223280192569605)
                      ·
                        rfl

theorem cell23_7356168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_7356168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356168 prefixEnd_7356168 := by exact prefixLift 7356168
  have htrace : WordTrace (prefixWord ++ tailWord_7356168) baseStart_7356168 baseEnd_7356168 := by
    simpa [prefixWord, tailWord_7356168, baseEnd_7356168] using wordTrace_append hprefix tailTrace_7356168
  have hstable : (prefixWord ++ tailWord_7356168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356168).length < 2 ^ (prefixWord ++ tailWord_7356168).sum := by decide
  have hdescent : baseEnd_7356168 < baseStart_7356168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356222 : List Nat := [4, 2, 1, 2, 2, 2, 1, 4, 5]
def baseStart_7356222 : Nat := 118140960795 + 7356222 * 2 ^ 59
def prefixEnd_7356222 : Nat := 4983230072969 + 3 ^ 40 * 7356222 * 2
def baseEnd_7356222 : Nat := 419697520797624775699373

theorem tailTrace_7356222 : CollatzResearch.WordTrace tailWord_7356222 prefixEnd_7356222 419697520797624775699373 := by
  unfold tailWord_7356222
  simp only [CollatzResearch.WordTrace]
  refine ⟨33537932294458938942519865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178868972237114341026772613 33537932294458938942519865)
  ·
    refine ⟨25153449220844204206889899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33537932294458938942519865 25153449220844204206889899)
    ·
      refine ⟨37730173831266306310334849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25153449220844204206889899 37730173831266306310334849)
      ·
        refine ⟨28297630373449729732751137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37730173831266306310334849 28297630373449729732751137)
        ·
          refine ⟨21223222780087297299563353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28297630373449729732751137 21223222780087297299563353)
          ·
            refine ⟨15917417085065472974672515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21223222780087297299563353 15917417085065472974672515)
            ·
              refine ⟨23876125627598209462008773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15917417085065472974672515 23876125627598209462008773)
              ·
                refine ⟨4476773555174664274126645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23876125627598209462008773 4476773555174664274126645)
                ·
                  refine ⟨419697520797624775699373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4476773555174664274126645 419697520797624775699373)
                  ·
                    rfl

theorem cell23_7356222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_7356222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356222 prefixEnd_7356222 := by exact prefixLift 7356222
  have htrace : WordTrace (prefixWord ++ tailWord_7356222) baseStart_7356222 baseEnd_7356222 := by
    simpa [prefixWord, tailWord_7356222, baseEnd_7356222] using wordTrace_append hprefix tailTrace_7356222
  have hstable : (prefixWord ++ tailWord_7356222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356222).length < 2 ^ (prefixWord ++ tailWord_7356222).sum := by decide
  have hdescent : baseEnd_7356222 < baseStart_7356222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356255 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 4]
def baseStart_7356255 : Nat := 118140960795 + 7356255 * 2 ^ 59
def prefixEnd_7356255 : Nat := 4983230072969 + 3 ^ 40 * 7356255 * 2
def baseEnd_7356255 : Nat := 3777294632040221352181705

theorem tailTrace_7356255 : CollatzResearch.WordTrace tailWord_7356255 prefixEnd_7356255 3777294632040221352181705 := by
  unfold tailWord_7356255
  simp only [CollatzResearch.WordTrace]
  refine ⟨268304661964551958176110219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178869774643034638784073479 268304661964551958176110219)
  ·
    refine ⟨402456992946827937264165329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268304661964551958176110219 402456992946827937264165329)
    ·
      refine ⟨301842744710120952948123997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402456992946827937264165329 301842744710120952948123997)
      ·
        refine ⟨113191029266295357355546499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301842744710120952948123997 113191029266295357355546499)
        ·
          refine ⟨169786543899443036033319749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113191029266295357355546499 169786543899443036033319749)
          ·
            refine ⟨31834976981145569256247453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169786543899443036033319749 31834976981145569256247453)
            ·
              refine ⟨11938116367929588471092795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31834976981145569256247453 11938116367929588471092795)
              ·
                refine ⟨17907174551894382706639193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11938116367929588471092795 17907174551894382706639193)
                ·
                  refine ⟨13430380913920787029979395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17907174551894382706639193 13430380913920787029979395)
                  ·
                    refine ⟨20145571370881180544969093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13430380913920787029979395 20145571370881180544969093)
                    ·
                      refine ⟨3777294632040221352181705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20145571370881180544969093 3777294632040221352181705)
                      ·
                        rfl

theorem cell23_7356255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_7356255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356255 prefixEnd_7356255 := by exact prefixLift 7356255
  have htrace : WordTrace (prefixWord ++ tailWord_7356255) baseStart_7356255 baseEnd_7356255 := by
    simpa [prefixWord, tailWord_7356255, baseEnd_7356255] using wordTrace_append hprefix tailTrace_7356255
  have hstable : (prefixWord ++ tailWord_7356255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356255).length < 2 ^ (prefixWord ++ tailWord_7356255).sum := by decide
  have hdescent : baseEnd_7356255 < baseStart_7356255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356268 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_7356268 : Nat := 118140960795 + 7356268 * 2 ^ 59
def prefixEnd_7356268 : Nat := 4983230072969 + 3 ^ 40 * 7356268 * 2
def baseEnd_7356268 : Nat := 3777301307288729801319145

theorem tailTrace_7356268 : CollatzResearch.WordTrace tailWord_7356268 prefixEnd_7356268 3777301307288729801319145 := by
  unfold tailWord_7356268
  simp only [CollatzResearch.WordTrace]
  refine ⟨134152568056752430698166729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178870090742336574264222305 134152568056752430698166729)
  ·
    refine ⟨100614426042564323023625047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134152568056752430698166729 100614426042564323023625047)
    ·
      refine ⟨150921639063846484535437571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100614426042564323023625047 150921639063846484535437571)
      ·
        refine ⟨226382458595769726803156357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150921639063846484535437571 226382458595769726803156357)
        ·
          refine ⟨42446710986706823775591817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226382458595769726803156357 42446710986706823775591817)
          ·
            refine ⟨31835033240030117831693863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42446710986706823775591817 31835033240030117831693863)
            ·
              refine ⟨47752549860045176747540795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31835033240030117831693863 47752549860045176747540795)
              ·
                refine ⟨71628824790067765121311193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47752549860045176747540795 71628824790067765121311193)
                ·
                  refine ⟨53721618592550823840983395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71628824790067765121311193 53721618592550823840983395)
                  ·
                    refine ⟨80582427888826235761475093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53721618592550823840983395 80582427888826235761475093)
                    ·
                      refine ⟨3777301307288729801319145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80582427888826235761475093 3777301307288729801319145)
                      ·
                        rfl

theorem cell23_7356268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_7356268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356268 prefixEnd_7356268 := by exact prefixLift 7356268
  have htrace : WordTrace (prefixWord ++ tailWord_7356268) baseStart_7356268 baseEnd_7356268 := by
    simpa [prefixWord, tailWord_7356268, baseEnd_7356268] using wordTrace_append hprefix tailTrace_7356268
  have hstable : (prefixWord ++ tailWord_7356268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356268).length < 2 ^ (prefixWord ++ tailWord_7356268).sum := by decide
  have hdescent : baseEnd_7356268 < baseStart_7356268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356282 : List Nat := [3, 1, 1, 1, 1, 1, 6, 4, 1, 4]
def baseStart_7356282 : Nat := 118140960795 + 7356282 * 2 ^ 59
def prefixEnd_7356282 : Nat := 4983230072969 + 3 ^ 40 * 7356282 * 2
def baseEnd_7356282 : Nat := 1259102832005964248848027

theorem tailTrace_7356282 : CollatzResearch.WordTrace tailWord_7356282 prefixEnd_7356282 1259102832005964248848027 := by
  unfold tailWord_7356282
  simp only [CollatzResearch.WordTrace]
  refine ⟨67076411683863535446835775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178870431156969427858228733 67076411683863535446835775)
  ·
    refine ⟨100614617525795303170253663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67076411683863535446835775 100614617525795303170253663)
    ·
      refine ⟨150921926288692954755380495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100614617525795303170253663 150921926288692954755380495)
      ·
        refine ⟨226382889433039432133070743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150921926288692954755380495 226382889433039432133070743)
        ·
          refine ⟨339574334149559148199606115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226382889433039432133070743 339574334149559148199606115)
          ·
            refine ⟨509361501224338722299409173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339574334149559148199606115 509361501224338722299409173)
            ·
              refine ⟨23876320369890877607784805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 509361501224338722299409173 23876320369890877607784805)
              ·
                refine ⟨4476810069354539551459651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23876320369890877607784805 4476810069354539551459651)
                ·
                  refine ⟨6715215104031809327189477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476810069354539551459651 6715215104031809327189477)
                  ·
                    refine ⟨1259102832005964248848027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6715215104031809327189477 1259102832005964248848027)
                    ·
                      rfl

theorem cell23_7356282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_7356282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356282 prefixEnd_7356282 := by exact prefixLift 7356282
  have htrace : WordTrace (prefixWord ++ tailWord_7356282) baseStart_7356282 baseEnd_7356282 := by
    simpa [prefixWord, tailWord_7356282, baseEnd_7356282] using wordTrace_append hprefix tailTrace_7356282
  have hstable : (prefixWord ++ tailWord_7356282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356282).length < 2 ^ (prefixWord ++ tailWord_7356282).sum := by decide
  have hdescent : baseEnd_7356282 < baseStart_7356282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356316 : List Nat := [2, 2, 3, 3, 1, 3, 1, 3, 1, 4]
def baseStart_7356316 : Nat := 118140960795 + 7356316 * 2 ^ 59
def prefixEnd_7356316 : Nat := 4983230072969 + 3 ^ 40 * 7356316 * 2
def baseEnd_7356316 : Nat := 1259108651453381871172975

theorem tailTrace_7356316 : CollatzResearch.WordTrace tailWord_7356316 prefixEnd_7356316 1259108651453381871172975 := by
  unfold tailWord_7356316
  simp only [CollatzResearch.WordTrace]
  refine ⟨134153443408665482797040401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178871257878220643729387201 134153443408665482797040401)
  ·
    refine ⟨100615082556499112097780301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134153443408665482797040401 100615082556499112097780301)
    ·
      refine ⟨37730655958687167036667613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100615082556499112097780301 37730655958687167036667613)
      ·
        refine ⟨14148995984507687638750355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37730655958687167036667613 14148995984507687638750355)
        ·
          refine ⟨21223493976761531458125533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14148995984507687638750355 21223493976761531458125533)
          ·
            refine ⟨7958810241285574296797075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21223493976761531458125533 7958810241285574296797075)
            ·
              refine ⟨11938215361928361445195613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7958810241285574296797075 11938215361928361445195613)
              ·
                refine ⟨4476830760723135541948355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11938215361928361445195613 4476830760723135541948355)
                ·
                  refine ⟨6715246141084703312922533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476830760723135541948355 6715246141084703312922533)
                  ·
                    refine ⟨1259108651453381871172975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6715246141084703312922533 1259108651453381871172975)
                    ·
                      rfl

theorem cell23_7356316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_7356316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356316 prefixEnd_7356316 := by exact prefixLift 7356316
  have htrace : WordTrace (prefixWord ++ tailWord_7356316) baseStart_7356316 baseEnd_7356316 := by
    simpa [prefixWord, tailWord_7356316, baseEnd_7356316] using wordTrace_append hprefix tailTrace_7356316
  have hstable : (prefixWord ++ tailWord_7356316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356316).length < 2 ^ (prefixWord ++ tailWord_7356316).sum := by decide
  have hdescent : baseEnd_7356316 < baseStart_7356316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356345 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 3, 1, 4]
def baseStart_7356345 : Nat := 118140960795 + 7356345 * 2 ^ 59
def prefixEnd_7356345 : Nat := 4983230072969 + 3 ^ 40 * 7356345 * 2
def baseEnd_7356345 : Nat := 3777340845299126000056291

theorem tailTrace_7356345 : CollatzResearch.WordTrace tailWord_7356345 prefixEnd_7356345 3777340845299126000056291 := by
  unfold tailWord_7356345
  simp only [CollatzResearch.WordTrace]
  refine ⟨268307944534225903546886489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178871963022817269031257659 268307944534225903546886489)
  ·
    refine ⟨201230958400669427660164867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268307944534225903546886489 201230958400669427660164867)
    ·
      refine ⟨301846437601004141490247301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201230958400669427660164867 301846437601004141490247301)
      ·
        refine ⟨56596207050188276529421369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301846437601004141490247301 56596207050188276529421369)
        ·
          refine ⟨42447155287641207397066027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56596207050188276529421369 42447155287641207397066027)
          ·
            refine ⟨63670732931461811095599041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42447155287641207397066027 63670732931461811095599041)
            ·
              refine ⟨47753049698596358321699281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63670732931461811095599041 47753049698596358321699281)
              ·
                refine ⟨35814787273947268741274461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47753049698596358321699281 35814787273947268741274461)
                ·
                  refine ⟨13430545227730225777977923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35814787273947268741274461 13430545227730225777977923)
                  ·
                    refine ⟨20145817841595338666966885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13430545227730225777977923 20145817841595338666966885)
                    ·
                      refine ⟨3777340845299126000056291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20145817841595338666966885 3777340845299126000056291)
                      ·
                        rfl

theorem cell23_7356345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_7356345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356345 prefixEnd_7356345 := by exact prefixLift 7356345
  have htrace : WordTrace (prefixWord ++ tailWord_7356345) baseStart_7356345 baseEnd_7356345 := by
    simpa [prefixWord, tailWord_7356345, baseEnd_7356345] using wordTrace_append hprefix tailTrace_7356345
  have hstable : (prefixWord ++ tailWord_7356345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356345).length < 2 ^ (prefixWord ++ tailWord_7356345).sum := by decide
  have hdescent : baseEnd_7356345 < baseStart_7356345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356362 : List Nat := [3, 1, 2, 1, 2, 1, 5, 2, 1, 1, 4]
def baseStart_7356362 : Nat := 118140960795 + 7356362 * 2 ^ 59
def prefixEnd_7356362 : Nat := 4983230072969 + 3 ^ 40 * 7356362 * 2
def baseEnd_7356362 : Nat := 3777349574470252433543713

theorem tailTrace_7356362 : CollatzResearch.WordTrace tailWord_7356362 prefixEnd_7356362 3777349574470252433543713 := by
  unfold tailWord_7356362
  simp only [CollatzResearch.WordTrace]
  refine ⟨67077141143791078862563835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178872376383442876966836893 67077141143791078862563835)
  ·
    refine ⟨100615711715686618293845753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67077141143791078862563835 100615711715686618293845753)
    ·
      refine ⟨75461783786764963720384315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100615711715686618293845753 75461783786764963720384315)
      ·
        refine ⟨113192675680147445580576473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75461783786764963720384315 113192675680147445580576473)
        ·
          refine ⟨84894506760110584185432355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113192675680147445580576473 84894506760110584185432355)
          ·
            refine ⟨127341760140165876278148533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84894506760110584185432355 127341760140165876278148533)
            ·
              refine ⟨11938290013140550901076425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127341760140165876278148533 11938290013140550901076425)
              ·
                refine ⟨8953717509855413175807319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11938290013140550901076425 8953717509855413175807319)
                ·
                  refine ⟨13430576264783119763710979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8953717509855413175807319 13430576264783119763710979)
                  ·
                    refine ⟨20145864397174679645566469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13430576264783119763710979 20145864397174679645566469)
                    ·
                      refine ⟨3777349574470252433543713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20145864397174679645566469 3777349574470252433543713)
                      ·
                        rfl

theorem cell23_7356362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_7356362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356362 prefixEnd_7356362 := by exact prefixLift 7356362
  have htrace : WordTrace (prefixWord ++ tailWord_7356362) baseStart_7356362 baseEnd_7356362 := by
    simpa [prefixWord, tailWord_7356362, baseEnd_7356362] using wordTrace_append hprefix tailTrace_7356362
  have hstable : (prefixWord ++ tailWord_7356362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356362).length < 2 ^ (prefixWord ++ tailWord_7356362).sum := by decide
  have hdescent : baseEnd_7356362 < baseStart_7356362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356368 : List Nat := [2, 1, 1, 1, 1, 2, 6, 9]
def baseStart_7356368 : Nat := 118140960795 + 7356368 * 2 ^ 59
def prefixEnd_7356368 : Nat := 4983230072969 + 3 ^ 40 * 7356368 * 2
def baseEnd_7356368 : Nat := 139901950198302941113655

theorem tailTrace_7356368 : CollatzResearch.WordTrace tailWord_7356368 prefixEnd_7356368 139901950198302941113655 := by
  unfold tailWord_7356368
  simp only [CollatzResearch.WordTrace]
  refine ⟨134154391706571289237486879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178872522275428385649982505 134154391706571289237486879)
  ·
    refine ⟨201231587559856933856230319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134154391706571289237486879 201231587559856933856230319)
    ·
      refine ⟨301847381339785400784345479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201231587559856933856230319 301847381339785400784345479)
      ·
        refine ⟨452771072009678101176518219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301847381339785400784345479 452771072009678101176518219)
        ·
          refine ⟨679156608014517151764777329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452771072009678101176518219 679156608014517151764777329)
          ·
            refine ⟨509367456010887863823582997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 679156608014517151764777329 509367456010887863823582997)
            ·
              refine ⟨23876599500510368616730453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 509367456010887863823582997 23876599500510368616730453)
              ·
                refine ⟨139901950198302941113655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23876599500510368616730453 139901950198302941113655)
                ·
                  rfl

theorem cell23_7356368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 9].length) (baseStart_7356368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356368 prefixEnd_7356368 := by exact prefixLift 7356368
  have htrace : WordTrace (prefixWord ++ tailWord_7356368) baseStart_7356368 baseEnd_7356368 := by
    simpa [prefixWord, tailWord_7356368, baseEnd_7356368] using wordTrace_append hprefix tailTrace_7356368
  have hstable : (prefixWord ++ tailWord_7356368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356368).length < 2 ^ (prefixWord ++ tailWord_7356368).sum := by decide
  have hdescent : baseEnd_7356368 < baseStart_7356368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356375 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 4]
def baseStart_7356375 : Nat := 118140960795 + 7356375 * 2 ^ 59
def prefixEnd_7356375 : Nat := 4983230072969 + 3 ^ 40 * 7356375 * 2
def baseEnd_7356375 : Nat := 3777356249718760882681153

theorem tailTrace_7356375 : CollatzResearch.WordTrace tailWord_7356375 prefixEnd_7356375 3777356249718760882681153 := by
  unfold tailWord_7356375
  simp only [CollatzResearch.WordTrace]
  refine ⟨268309038724117218670478579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178872692482744812446985719 268309038724117218670478579)
  ·
    refine ⟨402463558086175828005717869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268309038724117218670478579 402463558086175828005717869)
    ·
      refine ⟨150923834282315935502144201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402463558086175828005717869 150923834282315935502144201)
      ·
        refine ⟨113192875711736951626608151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150923834282315935502144201 113192875711736951626608151)
        ·
          refine ⟨169789313567605427439912227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113192875711736951626608151 169789313567605427439912227)
          ·
            refine ⟨254683970351408141159868341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169789313567605427439912227 254683970351408141159868341)
            ·
              refine ⟨23876622220444513233737657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254683970351408141159868341 23876622220444513233737657)
              ·
                refine ⟨17907466665333384925303243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23876622220444513233737657 17907466665333384925303243)
                ·
                  refine ⟨26861199998000077387954865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17907466665333384925303243 26861199998000077387954865)
                  ·
                    refine ⟨20145899998500058040966149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26861199998000077387954865 20145899998500058040966149)
                    ·
                      refine ⟨3777356249718760882681153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20145899998500058040966149 3777356249718760882681153)
                      ·
                        rfl

theorem cell23_7356375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_7356375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356375 prefixEnd_7356375 := by exact prefixLift 7356375
  have htrace : WordTrace (prefixWord ++ tailWord_7356375) baseStart_7356375 baseEnd_7356375 := by
    simpa [prefixWord, tailWord_7356375, baseEnd_7356375] using wordTrace_append hprefix tailTrace_7356375
  have hstable : (prefixWord ++ tailWord_7356375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356375).length < 2 ^ (prefixWord ++ tailWord_7356375).sum := by decide
  have hdescent : baseEnd_7356375 < baseStart_7356375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356412 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_7356412 : Nat := 118140960795 + 7356412 * 2 ^ 59
def prefixEnd_7356412 : Nat := 4983230072969 + 3 ^ 40 * 7356412 * 2
def baseEnd_7356412 : Nat := 3777375248502977237918483

theorem tailTrace_7356412 : CollatzResearch.WordTrace tailWord_7356412 prefixEnd_7356412 3777375248502977237918483 := by
  unfold tailWord_7356412
  simp only [CollatzResearch.WordTrace]
  refine ⟨134155194112491586994787745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178873592149988782659716993 134155194112491586994787745)
  ·
    refine ⟨100616395584368690246090809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134155194112491586994787745 100616395584368690246090809)
    ·
      refine ⟨75462296688276517684568107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100616395584368690246090809 75462296688276517684568107)
      ·
        refine ⟨113193445032414776526852161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75462296688276517684568107 113193445032414776526852161)
        ·
          refine ⟨84895083774311082395139121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113193445032414776526852161 84895083774311082395139121)
          ·
            refine ⟨63671312830733311796354341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84895083774311082395139121 63671312830733311796354341)
            ·
              refine ⟨11938371155762495961816439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63671312830733311796354341 11938371155762495961816439)
              ·
                refine ⟨17907556733643743942724659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11938371155762495961816439 17907556733643743942724659)
                ·
                  refine ⟨26861335100465615914086989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17907556733643743942724659 26861335100465615914086989)
                  ·
                    refine ⟨10073000662674605967782621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26861335100465615914086989 10073000662674605967782621)
                    ·
                      refine ⟨3777375248502977237918483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10073000662674605967782621 3777375248502977237918483)
                      ·
                        rfl

theorem cell23_7356412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_7356412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356412 prefixEnd_7356412 := by exact prefixLift 7356412
  have htrace : WordTrace (prefixWord ++ tailWord_7356412) baseStart_7356412 baseEnd_7356412 := by
    simpa [prefixWord, tailWord_7356412, baseEnd_7356412] using wordTrace_append hprefix tailTrace_7356412
  have hstable : (prefixWord ++ tailWord_7356412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356412).length < 2 ^ (prefixWord ++ tailWord_7356412).sum := by decide
  have hdescent : baseEnd_7356412 < baseStart_7356412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356462 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_7356462 : Nat := 118140960795 + 7356462 * 2 ^ 59
def prefixEnd_7356462 : Nat := 4983230072969 + 3 ^ 40 * 7356462 * 2
def baseEnd_7356462 : Nat := 1259133640845234014097751

theorem tailTrace_7356462 : CollatzResearch.WordTrace tailWord_7356462 prefixEnd_7356462 1259133640845234014097751 := by
  unfold tailWord_7356462
  simp only [CollatzResearch.WordTrace]
  refine ⟨33539026484350254066111955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178874807916534688352597093 33539026484350254066111955)
  ·
    refine ⟨50308539726525381099167933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33539026484350254066111955 50308539726525381099167933)
    ·
      refine ⟨18865702397447017912187975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50308539726525381099167933 18865702397447017912187975)
      ·
        refine ⟨28298553596170526868281963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18865702397447017912187975 28298553596170526868281963)
        ·
          refine ⟨42447830394255790302422945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28298553596170526868281963 42447830394255790302422945)
          ·
            refine ⟨31835872795691842726817209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42447830394255790302422945 31835872795691842726817209)
            ·
              refine ⟨23876904596768882045112907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31835872795691842726817209 23876904596768882045112907)
              ·
                refine ⟨35815356895153323067669361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23876904596768882045112907 35815356895153323067669361)
                ·
                  refine ⟨26861517671364992300752021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35815356895153323067669361 26861517671364992300752021)
                  ·
                    refine ⟨1259133640845234014097751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26861517671364992300752021 1259133640845234014097751)
                    ·
                      rfl

theorem cell23_7356462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_7356462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356462 prefixEnd_7356462 := by exact prefixLift 7356462
  have htrace : WordTrace (prefixWord ++ tailWord_7356462) baseStart_7356462 baseEnd_7356462 := by
    simpa [prefixWord, tailWord_7356462, baseEnd_7356462] using wordTrace_append hprefix tailTrace_7356462
  have hstable : (prefixWord ++ tailWord_7356462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356462).length < 2 ^ (prefixWord ++ tailWord_7356462).sum := by decide
  have hdescent : baseEnd_7356462 < baseStart_7356462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356469 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_7356469 : Nat := 118140960795 + 7356469 * 2 ^ 59
def prefixEnd_7356469 : Nat := 4983230072969 + 3 ^ 40 * 7356469 * 2
def baseEnd_7356469 : Nat := 3777404516900283514905721

theorem tailTrace_7356469 : CollatzResearch.WordTrace tailWord_7356469 prefixEnd_7356469 3777404516900283514905721 := by
  unfold tailWord_7356469
  simp only [CollatzResearch.WordTrace]
  refine ⟨268312467185776672724400461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178874978123851115149600307 268312467185776672724400461)
  ·
    refine ⟨100617175194666252271650173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268312467185776672724400461 100617175194666252271650173)
    ·
      refine ⟨37731440697999844601868815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100617175194666252271650173 37731440697999844601868815)
      ·
        refine ⟨56597161046999766902803223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37731440697999844601868815 56597161046999766902803223)
        ·
          refine ⟨84895741570499650354204835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56597161046999766902803223 84895741570499650354204835)
          ·
            refine ⟨127343612355749475531307253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84895741570499650354204835 127343612355749475531307253)
            ·
              refine ⟨11938463658351513331060055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127343612355749475531307253 11938463658351513331060055)
              ·
                refine ⟨17907695487527269996590083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11938463658351513331060055 17907695487527269996590083)
                ·
                  refine ⟨26861543231290904994885125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17907695487527269996590083 26861543231290904994885125)
                  ·
                    refine ⟨5036539355867044686540961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26861543231290904994885125 5036539355867044686540961)
                    ·
                      refine ⟨3777404516900283514905721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5036539355867044686540961 3777404516900283514905721)
                      ·
                        rfl

theorem cell23_7356469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_7356469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356469 prefixEnd_7356469 := by exact prefixLift 7356469
  have htrace : WordTrace (prefixWord ++ tailWord_7356469) baseStart_7356469 baseEnd_7356469 := by
    simpa [prefixWord, tailWord_7356469, baseEnd_7356469] using wordTrace_append hprefix tailTrace_7356469
  have hstable : (prefixWord ++ tailWord_7356469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356469).length < 2 ^ (prefixWord ++ tailWord_7356469).sum := by decide
  have hdescent : baseEnd_7356469 < baseStart_7356469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356486 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_7356486 : Nat := 118140960795 + 7356486 * 2 ^ 59
def prefixEnd_7356486 : Nat := 4983230072969 + 3 ^ 40 * 7356486 * 2
def baseEnd_7356486 : Nat := 3777413246071409948393143

theorem tailTrace_7356486 : CollatzResearch.WordTrace tailWord_7356486 prefixEnd_7356486 3777413246071409948393143 := by
  unfold tailWord_7356486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8384783975834846394617791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178875391484476723085179541 8384783975834846394617791)
  ·
    refine ⟨12577175963752269591926687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8384783975834846394617791 12577175963752269591926687)
    ·
      refine ⟨18865763945628404387890031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12577175963752269591926687 18865763945628404387890031)
      ·
        refine ⟨28298645918442606581835047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18865763945628404387890031 28298645918442606581835047)
        ·
          refine ⟨42447968877663909872752571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28298645918442606581835047 42447968877663909872752571)
          ·
            refine ⟨63671953316495864809128857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42447968877663909872752571 63671953316495864809128857)
            ·
              refine ⟨47753964987371898606846643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63671953316495864809128857 47753964987371898606846643)
              ·
                refine ⟨71630947481057847910269965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47753964987371898606846643 71630947481057847910269965)
                ·
                  refine ⟨26861605305396692966351237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71630947481057847910269965 26861605305396692966351237)
                  ·
                    refine ⟨5036550994761879931190857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26861605305396692966351237 5036550994761879931190857)
                    ·
                      refine ⟨3777413246071409948393143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5036550994761879931190857 3777413246071409948393143)
                      ·
                        rfl

theorem cell23_7356486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_7356486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356486 prefixEnd_7356486 := by exact prefixLift 7356486
  have htrace : WordTrace (prefixWord ++ tailWord_7356486) baseStart_7356486 baseEnd_7356486 := by
    simpa [prefixWord, tailWord_7356486, baseEnd_7356486] using wordTrace_append hprefix tailTrace_7356486
  have hstable : (prefixWord ++ tailWord_7356486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356486).length < 2 ^ (prefixWord ++ tailWord_7356486).sum := by decide
  have hdescent : baseEnd_7356486 < baseStart_7356486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356509 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 7]
def baseStart_7356509 : Nat := 118140960795 + 7356509 * 2 ^ 59
def prefixEnd_7356509 : Nat := 4983230072969 + 3 ^ 40 * 7356509 * 2
def baseEnd_7356509 : Nat := 419713895125162595378393

theorem tailTrace_7356509 : CollatzResearch.WordTrace tailWord_7356509 prefixEnd_7356509 419713895125162595378393 := by
  unfold tailWord_7356509
  simp only [CollatzResearch.WordTrace]
  refine ⟨268313926105631759555856581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178875950737087839703904387 268313926105631759555856581)
  ·
    refine ⟨50308861144805954916723109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268313926105631759555856581 50308861144805954916723109)
    ·
      refine ⟨9432911464651116546885583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50308861144805954916723109 9432911464651116546885583)
      ·
        refine ⟨14149367196976674820328375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9432911464651116546885583 14149367196976674820328375)
        ·
          refine ⟨21224050795465012230492563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14149367196976674820328375 21224050795465012230492563)
          ·
            refine ⟨31836076193197518345738845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21224050795465012230492563 31836076193197518345738845)
            ·
              refine ⟨11938528572449069379652067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31836076193197518345738845 11938528572449069379652067)
              ·
                refine ⟨17907792858673604069478101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11938528572449069379652067 17907792858673604069478101)
                ·
                  refine ⟨419713895125162595378393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17907792858673604069478101 419713895125162595378393)
                  ·
                    rfl

theorem cell23_7356509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_7356509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356509 prefixEnd_7356509 := by exact prefixLift 7356509
  have htrace : WordTrace (prefixWord ++ tailWord_7356509) baseStart_7356509 baseEnd_7356509 := by
    simpa [prefixWord, tailWord_7356509, baseEnd_7356509] using wordTrace_append hprefix tailTrace_7356509
  have hstable : (prefixWord ++ tailWord_7356509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356509).length < 2 ^ (prefixWord ++ tailWord_7356509).sum := by decide
  have hdescent : baseEnd_7356509 < baseStart_7356509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356515 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 7]
def baseStart_7356515 : Nat := 118140960795 + 7356515 * 2 ^ 59
def prefixEnd_7356515 : Nat := 4983230072969 + 3 ^ 40 * 7356515 * 2
def baseEnd_7356515 : Nat := 3777428137010390334930509

theorem tailTrace_7356515 : CollatzResearch.WordTrace tailWord_7356515 prefixEnd_7356515 3777428137010390334930509 := by
  unfold tailWord_7356515
  simp only [CollatzResearch.WordTrace]
  refine ⟨268314144943610022580574999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178876096629073348387049999 268314144943610022580574999)
  ·
    refine ⟨402471217415415033870862499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268314144943610022580574999 402471217415415033870862499)
    ·
      refine ⟨603706826123122550806293749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402471217415415033870862499 603706826123122550806293749)
      ·
        refine ⟨56597514949042739138090039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 603706826123122550806293749 56597514949042739138090039)
        ·
          refine ⟨84896272423564108707135059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56597514949042739138090039 84896272423564108707135059)
          ·
            refine ⟨127344408635346163060702589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84896272423564108707135059 127344408635346163060702589)
            ·
              refine ⟨47754153238254811147763471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127344408635346163060702589 47754153238254811147763471)
              ·
                refine ⟨71631229857382216721645207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47754153238254811147763471 71631229857382216721645207)
                ·
                  refine ⟨107446844786073325082467811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71631229857382216721645207 107446844786073325082467811)
                  ·
                    refine ⟨161170267179109987623701717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107446844786073325082467811 161170267179109987623701717)
                    ·
                      refine ⟨3777428137010390334930509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161170267179109987623701717 3777428137010390334930509)
                      ·
                        rfl

theorem cell23_7356515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_7356515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356515 prefixEnd_7356515 := by exact prefixLift 7356515
  have htrace : WordTrace (prefixWord ++ tailWord_7356515) baseStart_7356515 baseEnd_7356515 := by
    simpa [prefixWord, tailWord_7356515, baseEnd_7356515] using wordTrace_append hprefix tailTrace_7356515
  have hstable : (prefixWord ++ tailWord_7356515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356515).length < 2 ^ (prefixWord ++ tailWord_7356515).sum := by decide
  have hdescent : baseEnd_7356515 < baseStart_7356515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356562 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_7356562 : Nat := 118140960795 + 7356562 * 2 ^ 59
def prefixEnd_7356562 : Nat := 4983230072969 + 3 ^ 40 * 7356562 * 2
def baseEnd_7356562 : Nat := 3777452270601151651042793

theorem tailTrace_7356562 : CollatzResearch.WordTrace tailWord_7356562 prefixEnd_7356562 3777452270601151651042793 := by
  unfold tailWord_7356562
  simp only [CollatzResearch.WordTrace]
  refine ⟨67078964793609937401883985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178877239449626499738357293 67078964793609937401883985)
  ·
    refine ⟨50309223595207453051412989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67078964793609937401883985 50309223595207453051412989)
    ·
      refine ⟨18865958848202794894279871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50309223595207453051412989 18865958848202794894279871)
      ·
        refine ⟨28298938272304192341419807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18865958848202794894279871 28298938272304192341419807)
        ·
          refine ⟨42448407408456288512129711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28298938272304192341419807 42448407408456288512129711)
          ·
            refine ⟨63672611112684432768194567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42448407408456288512129711 63672611112684432768194567)
            ·
              refine ⟨95508916669026649152291851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63672611112684432768194567 95508916669026649152291851)
              ·
                refine ⟨143263375003539973728437777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95508916669026649152291851 143263375003539973728437777)
                ·
                  refine ⟨107447531252654980296328333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143263375003539973728437777 107447531252654980296328333)
                  ·
                    refine ⟨40292824219745617611123125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107447531252654980296328333 40292824219745617611123125)
                    ·
                      refine ⟨3777452270601151651042793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40292824219745617611123125 3777452270601151651042793)
                      ·
                        rfl

theorem cell23_7356562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_7356562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356562 prefixEnd_7356562 := by exact prefixLift 7356562
  have htrace : WordTrace (prefixWord ++ tailWord_7356562) baseStart_7356562 baseEnd_7356562 := by
    simpa [prefixWord, tailWord_7356562, baseEnd_7356562] using wordTrace_append hprefix tailTrace_7356562
  have hstable : (prefixWord ++ tailWord_7356562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356562).length < 2 ^ (prefixWord ++ tailWord_7356562).sum := by decide
  have hdescent : baseEnd_7356562 < baseStart_7356562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356590 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 2, 5]
def baseStart_7356590 : Nat := 118140960795 + 7356590 * 2 ^ 59
def prefixEnd_7356590 : Nat := 4983230072969 + 3 ^ 40 * 7356590 * 2
def baseEnd_7356590 : Nat := 1259155549353159180497555

theorem tailTrace_7356590 : CollatzResearch.WordTrace tailWord_7356590 prefixEnd_7356590 1259155549353159180497555 := by
  unfold tailWord_7356590
  simp only [CollatzResearch.WordTrace]
  refine ⟨33539610052292288798694403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178877920278892206926370149 33539610052292288798694403)
  ·
    refine ⟨50309415078438433198041605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33539610052292288798694403 50309415078438433198041605)
    ·
      refine ⟨9433015327207206224632801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50309415078438433198041605 9433015327207206224632801)
      ·
        refine ⟨7074761495405404668474601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9433015327207206224632801 7074761495405404668474601)
        ·
          refine ⟨5306071121554053501355951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7074761495405404668474601 5306071121554053501355951)
          ·
            refine ⟨7959106682331080252033927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306071121554053501355951 7959106682331080252033927)
            ·
              refine ⟨11938660023496620378050891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959106682331080252033927 11938660023496620378050891)
              ·
                refine ⟨17907990035244930567076337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11938660023496620378050891 17907990035244930567076337)
                ·
                  refine ⟨13430992526433697925307253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17907990035244930567076337 13430992526433697925307253)
                  ·
                    refine ⟨1259155549353159180497555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13430992526433697925307253 1259155549353159180497555)
                    ·
                      rfl

theorem cell23_7356590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_7356590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356590 prefixEnd_7356590 := by exact prefixLift 7356590
  have htrace : WordTrace (prefixWord ++ tailWord_7356590) baseStart_7356590 baseEnd_7356590 := by
    simpa [prefixWord, tailWord_7356590, baseEnd_7356590] using wordTrace_append hprefix tailTrace_7356590
  have hstable : (prefixWord ++ tailWord_7356590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356590).length < 2 ^ (prefixWord ++ tailWord_7356590).sum := by decide
  have hdescent : baseEnd_7356590 < baseStart_7356590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356593 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 2, 1, 4]
def baseStart_7356593 : Nat := 118140960795 + 7356593 * 2 ^ 59
def prefixEnd_7356593 : Nat := 4983230072969 + 3 ^ 40 * 7356593 * 2
def baseEnd_7356593 : Nat := 3777468188501441029755151

theorem tailTrace_7356593 : CollatzResearch.WordTrace tailWord_7356593 prefixEnd_7356593 3777468188501441029755151 := by
  unfold tailWord_7356593
  simp only [CollatzResearch.WordTrace]
  refine ⟨268316989837327441901914433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178877993224884961267942955 268316989837327441901914433)
  ·
    refine ⟨201237742377995581426435825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268316989837327441901914433 201237742377995581426435825)
    ·
      refine ⟨150928306783496686069826869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201237742377995581426435825 150928306783496686069826869)
      ·
        refine ⟨14149528760952814319046269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150928306783496686069826869 14149528760952814319046269)
        ·
          refine ⟨5306073285357305369642351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14149528760952814319046269 5306073285357305369642351)
          ·
            refine ⟨7959109928035958054463527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306073285357305369642351 7959109928035958054463527)
            ·
              refine ⟨11938664892053937081695291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959109928035958054463527 11938664892053937081695291)
              ·
                refine ⟨17907997338080905622542937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11938664892053937081695291 17907997338080905622542937)
                ·
                  refine ⟨13430998003560679216907203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17907997338080905622542937 13430998003560679216907203)
                  ·
                    refine ⟨20146497005341018825360805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13430998003560679216907203 20146497005341018825360805)
                    ·
                      refine ⟨3777468188501441029755151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20146497005341018825360805 3777468188501441029755151)
                      ·
                        rfl

theorem cell23_7356593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_7356593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356593 prefixEnd_7356593 := by exact prefixLift 7356593
  have htrace : WordTrace (prefixWord ++ tailWord_7356593) baseStart_7356593 baseEnd_7356593 := by
    simpa [prefixWord, tailWord_7356593, baseEnd_7356593] using wordTrace_append hprefix tailTrace_7356593
  have hstable : (prefixWord ++ tailWord_7356593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356593).length < 2 ^ (prefixWord ++ tailWord_7356593).sum := by decide
  have hdescent : baseEnd_7356593 < baseStart_7356593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356619 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 4, 3, 2]
def baseStart_7356619 : Nat := 118140960795 + 7356619 * 2 ^ 59
def prefixEnd_7356619 : Nat := 4983230072969 + 3 ^ 40 * 7356619 * 2
def baseEnd_7356619 : Nat := 3777481538998457928030031

theorem tailTrace_7356619 : CollatzResearch.WordTrace tailWord_7356619 prefixEnd_7356619 3777481538998457928030031 := by
  unfold tailWord_7356619
  simp only [CollatzResearch.WordTrace]
  refine ⟨268317938135233248342360911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178878625423488832228240607 268317938135233248342360911)
  ·
    refine ⟨402476907202849872513541367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268317938135233248342360911 402476907202849872513541367)
    ·
      refine ⟨603715360804274808770312051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402476907202849872513541367 603715360804274808770312051)
      ·
        refine ⟨905573041206412213155468077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603715360804274808770312051 905573041206412213155468077)
        ·
          refine ⟨339589890452404579933300529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 905573041206412213155468077 339589890452404579933300529)
          ·
            refine ⟨254692417839303434949975397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339589890452404579933300529 254692417839303434949975397)
            ·
              refine ⟨47754828344869394053120387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254692417839303434949975397 47754828344869394053120387)
              ·
                refine ⟨71632242517304091079680581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47754828344869394053120387 71632242517304091079680581)
                ·
                  refine ⟨13431045471994517077440109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71632242517304091079680581 13431045471994517077440109)
                  ·
                    refine ⟨5036642051997943904040041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13431045471994517077440109 5036642051997943904040041)
                    ·
                      refine ⟨3777481538998457928030031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5036642051997943904040041 3777481538998457928030031)
                      ·
                        rfl

theorem cell23_7356619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 3, 2].length) (baseStart_7356619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356619 prefixEnd_7356619 := by exact prefixLift 7356619
  have htrace : WordTrace (prefixWord ++ tailWord_7356619) baseStart_7356619 baseEnd_7356619 := by
    simpa [prefixWord, tailWord_7356619, baseEnd_7356619] using wordTrace_append hprefix tailTrace_7356619
  have hstable : (prefixWord ++ tailWord_7356619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356619).length < 2 ^ (prefixWord ++ tailWord_7356619).sum := by decide
  have hdescent : baseEnd_7356619 < baseStart_7356619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356626 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_7356626 : Nat := 118140960795 + 7356626 * 2 ^ 59
def prefixEnd_7356626 : Nat := 4983230072969 + 3 ^ 40 * 7356626 * 2
def baseEnd_7356626 : Nat := 3777485133363039400642499

theorem tailTrace_7356626 : CollatzResearch.WordTrace tailWord_7356626 prefixEnd_7356626 3777485133363039400642499 := by
  unfold tailWord_7356626
  simp only [CollatzResearch.WordTrace]
  refine ⟨67079548361551972134466433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178878795630805259025243821 67079548361551972134466433)
  ·
    refine ⟨50309661271163979100849825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67079548361551972134466433 50309661271163979100849825)
    ·
      refine ⟨37732245953372984325637369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50309661271163979100849825 37732245953372984325637369)
      ·
        refine ⟨28299184465029738244228027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37732245953372984325637369 28299184465029738244228027)
        ·
          refine ⟨42448776697544607366342041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28299184465029738244228027 42448776697544607366342041)
          ·
            refine ⟨31836582523158455524756531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42448776697544607366342041 31836582523158455524756531)
            ·
              refine ⟨47754873784737683287134797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31836582523158455524756531 47754873784737683287134797)
              ·
                refine ⟨17908077669276631232675549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47754873784737683287134797 17908077669276631232675549)
                ·
                  refine ⟨6715529125978736712253331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17908077669276631232675549 6715529125978736712253331)
                  ·
                    refine ⟨10073293688968105068379997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6715529125978736712253331 10073293688968105068379997)
                    ·
                      refine ⟨3777485133363039400642499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10073293688968105068379997 3777485133363039400642499)
                      ·
                        rfl

theorem cell23_7356626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_7356626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356626 prefixEnd_7356626 := by exact prefixLift 7356626
  have htrace : WordTrace (prefixWord ++ tailWord_7356626) baseStart_7356626 baseEnd_7356626 := by
    simpa [prefixWord, tailWord_7356626, baseEnd_7356626] using wordTrace_append hprefix tailTrace_7356626
  have hstable : (prefixWord ++ tailWord_7356626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356626).length < 2 ^ (prefixWord ++ tailWord_7356626).sum := by decide
  have hdescent : baseEnd_7356626 < baseStart_7356626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356652 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_7356652 : Nat := 118140960795 + 7356652 * 2 ^ 59
def prefixEnd_7356652 : Nat := 4983230072969 + 3 ^ 40 * 7356652 * 2
def baseEnd_7356652 : Nat := 3777498483860056298917379

theorem tailTrace_7356652 : CollatzResearch.WordTrace tailWord_7356652 prefixEnd_7356652 3777498483860056298917379 := by
  unfold tailWord_7356652
  simp only [CollatzResearch.WordTrace]
  refine ⟨134159570872056847489156105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178879427829409129985541473 134159570872056847489156105)
  ·
    refine ⟨100619678154042635616867079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134159570872056847489156105 100619678154042635616867079)
    ·
      refine ⟨150929517231063953425300619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100619678154042635616867079 150929517231063953425300619)
      ·
        refine ⟨226394275846595930137950929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150929517231063953425300619 226394275846595930137950929)
        ·
          refine ⟨169795706884946947603463197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226394275846595930137950929 169795706884946947603463197)
          ·
            refine ⟨63673390081855105351298699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169795706884946947603463197 63673390081855105351298699)
            ·
              refine ⟨95510085122782658026948049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63673390081855105351298699 95510085122782658026948049)
              ·
                refine ⟨71632563842086993520211037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95510085122782658026948049 71632563842086993520211037)
                ·
                  refine ⟨26862211440782622570079139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71632563842086993520211037 26862211440782622570079139)
                  ·
                    refine ⟨40293317161173933855118709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26862211440782622570079139 40293317161173933855118709)
                    ·
                      refine ⟨3777498483860056298917379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40293317161173933855118709 3777498483860056298917379)
                      ·
                        rfl

theorem cell23_7356652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_7356652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356652 prefixEnd_7356652 := by exact prefixLift 7356652
  have htrace : WordTrace (prefixWord ++ tailWord_7356652) baseStart_7356652 baseEnd_7356652 := by
    simpa [prefixWord, tailWord_7356652, baseEnd_7356652] using wordTrace_append hprefix tailTrace_7356652
  have hstable : (prefixWord ++ tailWord_7356652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356652).length < 2 ^ (prefixWord ++ tailWord_7356652).sum := by decide
  have hdescent : baseEnd_7356652 < baseStart_7356652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356703 : List Nat := [1, 1, 2, 4, 3, 3, 1, 2, 1, 2, 3]
def baseStart_7356703 : Nat := 118140960795 + 7356703 * 2 ^ 59
def prefixEnd_7356703 : Nat := 4983230072969 + 3 ^ 40 * 7356703 * 2
def baseEnd_7356703 : Nat := 3777524671373435599379645

theorem tailTrace_7356703 : CollatzResearch.WordTrace tailWord_7356703 prefixEnd_7356703 3777524671373435599379645 := by
  unfold tailWord_7356703
  simp only [CollatzResearch.WordTrace]
  refine ⟨268321001866928930688418763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178880667911285953792279175 268321001866928930688418763)
  ·
    refine ⟨402481502800393396032628145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268321001866928930688418763 402481502800393396032628145)
    ·
      refine ⟨301861127100295047024471109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402481502800393396032628145 301861127100295047024471109)
      ·
        refine ⟨56598961331305321317088333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301861127100295047024471109 56598961331305321317088333)
        ·
          refine ⟨21224610499239495493908125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56598961331305321317088333 21224610499239495493908125)
          ·
            refine ⟨7959228937214810810215547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21224610499239495493908125 7959228937214810810215547)
            ·
              refine ⟨11938843405822216215323321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959228937214810810215547 11938843405822216215323321)
              ·
                refine ⟨8954132554366662161492491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11938843405822216215323321 8954132554366662161492491)
                ·
                  refine ⟨13431198831549993242238737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8954132554366662161492491 13431198831549993242238737)
                  ·
                    refine ⟨10073399123662494931679053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13431198831549993242238737 10073399123662494931679053)
                    ·
                      refine ⟨3777524671373435599379645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10073399123662494931679053 3777524671373435599379645)
                      ·
                        rfl

theorem cell23_7356703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_7356703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356703 prefixEnd_7356703 := by exact prefixLift 7356703
  have htrace : WordTrace (prefixWord ++ tailWord_7356703) baseStart_7356703 baseEnd_7356703 := by
    simpa [prefixWord, tailWord_7356703, baseEnd_7356703] using wordTrace_append hprefix tailTrace_7356703
  have hstable : (prefixWord ++ tailWord_7356703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356703).length < 2 ^ (prefixWord ++ tailWord_7356703).sum := by decide
  have hdescent : baseEnd_7356703 < baseStart_7356703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356734 : List Nat := [4, 2, 1, 2, 1, 4, 2, 2, 1, 2, 2]
def baseStart_7356734 : Nat := 118140960795 + 7356734 * 2 ^ 59
def prefixEnd_7356734 : Nat := 4983230072969 + 3 ^ 40 * 7356734 * 2
def baseEnd_7356734 : Nat := 3777540589273724978092003

theorem tailTrace_7356734 : CollatzResearch.WordTrace tailWord_7356734 prefixEnd_7356734 3777540589273724978092003 := by
  unfold tailWord_7356734
  simp only [CollatzResearch.WordTrace]
  refine ⟨33540266566227077872849657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178881421686544415321864837 33540266566227077872849657)
  ·
    refine ⟨25155199924670308404637243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33540266566227077872849657 25155199924670308404637243)
    ·
      refine ⟨37732799887005462606955865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25155199924670308404637243 37732799887005462606955865)
      ·
        refine ⟨28299599915254096955216899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37732799887005462606955865 28299599915254096955216899)
        ·
          refine ⟨42449399872881145432825349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28299599915254096955216899 42449399872881145432825349)
          ·
            refine ⟨7959262476165214768654753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42449399872881145432825349 7959262476165214768654753)
            ·
              refine ⟨5969446857123911076491065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7959262476165214768654753 5969446857123911076491065)
              ·
                refine ⟨4477085142842933307368299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5969446857123911076491065 4477085142842933307368299)
                ·
                  refine ⟨6715627714264399961052449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4477085142842933307368299 6715627714264399961052449)
                  ·
                    refine ⟨5036720785698299970789337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6715627714264399961052449 5036720785698299970789337)
                    ·
                      refine ⟨3777540589273724978092003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5036720785698299970789337 3777540589273724978092003)
                      ·
                        rfl

theorem cell23_7356734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_7356734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356734 prefixEnd_7356734 := by exact prefixLift 7356734
  have htrace : WordTrace (prefixWord ++ tailWord_7356734) baseStart_7356734 baseEnd_7356734 := by
    simpa [prefixWord, tailWord_7356734, baseEnd_7356734] using wordTrace_append hprefix tailTrace_7356734
  have hstable : (prefixWord ++ tailWord_7356734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356734).length < 2 ^ (prefixWord ++ tailWord_7356734).sum := by decide
  have hdescent : baseEnd_7356734 < baseStart_7356734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356759 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 3]
def baseStart_7356759 : Nat := 118140960795 + 7356759 * 2 ^ 59
def prefixEnd_7356759 : Nat := 4983230072969 + 3 ^ 40 * 7356759 * 2
def baseEnd_7356759 : Nat := 3777553426290087380279387

theorem tailTrace_7356759 : CollatzResearch.WordTrace tailWord_7356759 prefixEnd_7356759 3777553426290087380279387 := by
  unfold tailWord_7356759
  simp only [CollatzResearch.WordTrace]
  refine ⟨268323044354726052252457331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178882029569817368168304887 268323044354726052252457331)
  ·
    refine ⟨402484566532089078378685997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268323044354726052252457331 402484566532089078378685997)
    ·
      refine ⟨150931712449533404392007249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402484566532089078378685997 150931712449533404392007249)
      ·
        refine ⟨113198784337150053294005437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150931712449533404392007249 113198784337150053294005437)
        ·
          refine ⟨42449544126431269985252039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113198784337150053294005437 42449544126431269985252039)
          ·
            refine ⟨63674316189646904977878059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42449544126431269985252039 63674316189646904977878059)
            ·
              refine ⟨95511474284470357466817089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63674316189646904977878059 95511474284470357466817089)
              ·
                refine ⟨71633605713352768100112817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95511474284470357466817089 71633605713352768100112817)
                ·
                  refine ⟨53725204285014576075084613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71633605713352768100112817 53725204285014576075084613)
                  ·
                    refine ⟨10073475803440233014078365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53725204285014576075084613 10073475803440233014078365)
                    ·
                      refine ⟨3777553426290087380279387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10073475803440233014078365 3777553426290087380279387)
                      ·
                        rfl

theorem cell23_7356759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_7356759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356759 prefixEnd_7356759 := by exact prefixLift 7356759
  have htrace : WordTrace (prefixWord ++ tailWord_7356759) baseStart_7356759 baseEnd_7356759 := by
    simpa [prefixWord, tailWord_7356759, baseEnd_7356759] using wordTrace_append hprefix tailTrace_7356759
  have hstable : (prefixWord ++ tailWord_7356759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356759).length < 2 ^ (prefixWord ++ tailWord_7356759).sum := by decide
  have hdescent : baseEnd_7356759 < baseStart_7356759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356809 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 1, 7]
def baseStart_7356809 : Nat := 118140960795 + 7356809 * 2 ^ 59
def prefixEnd_7356809 : Nat := 4983230072969 + 3 ^ 40 * 7356809 * 2
def baseEnd_7356809 : Nat := 1259193033440937394884719

theorem tailTrace_7356809 : CollatzResearch.WordTrace tailWord_7356809 prefixEnd_7356809 1259193033440937394884719 := by
  unfold tailWord_7356809
  simp only [CollatzResearch.WordTrace]
  refine ⟨268324868004544910791777481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178883245336363273861184987 268324868004544910791777481)
  ·
    refine ⟨201243651003408683093833111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268324868004544910791777481 201243651003408683093833111)
    ·
      refine ⟨301865476505113024640749667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201243651003408683093833111 301865476505113024640749667)
      ·
        refine ⟨452798214757669536961124501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301865476505113024640749667 452798214757669536961124501)
        ·
          refine ⟨21224916316765759545052711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 452798214757669536961124501 21224916316765759545052711)
          ·
            refine ⟨31837374475148639317579067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21224916316765759545052711 31837374475148639317579067)
            ·
              refine ⟨47756061712722958976368601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31837374475148639317579067 47756061712722958976368601)
              ·
                refine ⟨35817046284542219232276451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47756061712722958976368601 35817046284542219232276451)
                ·
                  refine ⟨53725569426813328848414677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35817046284542219232276451 53725569426813328848414677)
                  ·
                    refine ⟨1259193033440937394884719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53725569426813328848414677 1259193033440937394884719)
                    ·
                      rfl

theorem cell23_7356809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 7].length) (baseStart_7356809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356809 prefixEnd_7356809 := by exact prefixLift 7356809
  have htrace : WordTrace (prefixWord ++ tailWord_7356809) baseStart_7356809 baseEnd_7356809 := by
    simpa [prefixWord, tailWord_7356809, baseEnd_7356809] using wordTrace_append hprefix tailTrace_7356809
  have hstable : (prefixWord ++ tailWord_7356809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356809).length < 2 ^ (prefixWord ++ tailWord_7356809).sum := by decide
  have hdescent : baseEnd_7356809 < baseStart_7356809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356830 : List Nat := [4, 3, 1, 2, 1, 1, 3, 3, 5]
def baseStart_7356830 : Nat := 118140960795 + 7356830 * 2 ^ 59
def prefixEnd_7356830 : Nat := 4983230072969 + 3 ^ 40 * 7356830 * 2
def baseEnd_7356830 : Nat := 419732209268506289165729

theorem tailTrace_7356830 : CollatzResearch.WordTrace tailWord_7356830 prefixEnd_7356830 419732209268506289165729 := by
  unfold tailWord_7356830
  simp only [CollatzResearch.WordTrace]
  refine ⟨33540704242183603922286493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178883755958312554252194629 33540704242183603922286493)
  ·
    refine ⟨12577764090818851470857435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33540704242183603922286493 12577764090818851470857435)
    ·
      refine ⟨18866646136228277206286153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12577764090818851470857435 18866646136228277206286153)
      ·
        refine ⟨14149984602171207904714615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18866646136228277206286153 14149984602171207904714615)
        ·
          refine ⟨21224976903256811857071923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14149984602171207904714615 21224976903256811857071923)
          ·
            refine ⟨31837465354885217785607885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21224976903256811857071923 31837465354885217785607885)
            ·
              refine ⟨11939049508081956669602957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31837465354885217785607885 11939049508081956669602957)
              ·
                refine ⟨4477143565530733751101109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11939049508081956669602957 4477143565530733751101109)
                ·
                  refine ⟨419732209268506289165729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4477143565530733751101109 419732209268506289165729)
                  ·
                    rfl

theorem cell23_7356830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_7356830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356830 prefixEnd_7356830 := by exact prefixLift 7356830
  have htrace : WordTrace (prefixWord ++ tailWord_7356830) baseStart_7356830 baseEnd_7356830 := by
    simpa [prefixWord, tailWord_7356830, baseEnd_7356830] using wordTrace_append hprefix tailTrace_7356830
  have hstable : (prefixWord ++ tailWord_7356830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356830).length < 2 ^ (prefixWord ++ tailWord_7356830).sum := by decide
  have hdescent : baseEnd_7356830 < baseStart_7356830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356913 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 3, 1, 3]
def baseStart_7356913 : Nat := 118140960795 + 7356913 * 2 ^ 59
def prefixEnd_7356913 : Nat := 4983230072969 + 3 ^ 40 * 7356913 * 2
def baseEnd_7356913 : Nat := 3777632502310879777753679

theorem tailTrace_7356913 : CollatzResearch.WordTrace tailWord_7356913 prefixEnd_7356913 3777632502310879777753679 := by
  unfold tailWord_7356913
  simp only [CollatzResearch.WordTrace]
  refine ⟨268328661196168136553563393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178885774130778757702375595 268328661196168136553563393)
  ·
    refine ⟨201246495897126102415172545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268328661196168136553563393 201246495897126102415172545)
    ·
      refine ⟨150934871922844576811379409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201246495897126102415172545 150934871922844576811379409)
      ·
        refine ⟨113201153942133432608534557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150934871922844576811379409 113201153942133432608534557)
        ·
          refine ⟨42450432728300037228200459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113201153942133432608534557 42450432728300037228200459)
          ·
            refine ⟨63675649092450055842300689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42450432728300037228200459 63675649092450055842300689)
            ·
              refine ⟨47756736819337541881725517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63675649092450055842300689 47756736819337541881725517)
              ·
                refine ⟨17908776307251578205647069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47756736819337541881725517 17908776307251578205647069)
                ·
                  refine ⟨6715791115219341827117651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17908776307251578205647069 6715791115219341827117651)
                  ·
                    refine ⟨10073686672829012740676477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6715791115219341827117651 10073686672829012740676477)
                    ·
                      refine ⟨3777632502310879777753679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10073686672829012740676477 3777632502310879777753679)
                      ·
                        rfl

theorem cell23_7356913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_7356913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356913 prefixEnd_7356913 := by exact prefixLift 7356913
  have htrace : WordTrace (prefixWord ++ tailWord_7356913) baseStart_7356913 baseEnd_7356913 := by
    simpa [prefixWord, tailWord_7356913, baseEnd_7356913] using wordTrace_append hprefix tailTrace_7356913
  have hstable : (prefixWord ++ tailWord_7356913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356913).length < 2 ^ (prefixWord ++ tailWord_7356913).sum := by decide
  have hdescent : baseEnd_7356913 < baseStart_7356913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356934 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_7356934 : Nat := 118140960795 + 7356934 * 2 ^ 59
def prefixEnd_7356934 : Nat := 4983230072969 + 3 ^ 40 * 7356934 * 2
def baseEnd_7356934 : Nat := 3777643285404624195591083

theorem tailTrace_7356934 : CollatzResearch.WordTrace tailWord_7356934 prefixEnd_7356934 3777643285404624195591083 := by
  unfold tailWord_7356934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8385294597784126785627433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178886284752728038093385237 8385294597784126785627433)
  ·
    refine ⟨6288970948338095089220575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8385294597784126785627433 6288970948338095089220575)
    ·
      refine ⟨9433456422507142633830863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6288970948338095089220575 9433456422507142633830863)
      ·
        refine ⟨14150184633760713950746295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9433456422507142633830863 14150184633760713950746295)
        ·
          refine ⟨21225276950641070926119443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14150184633760713950746295 21225276950641070926119443)
          ·
            refine ⟨31837915425961606389179165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21225276950641070926119443 31837915425961606389179165)
            ·
              refine ⟨11939218284735602395942187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31837915425961606389179165 11939218284735602395942187)
              ·
                refine ⟨17908827427103403593913281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11939218284735602395942187 17908827427103403593913281)
                ·
                  refine ⟨13431620570327552695434961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17908827427103403593913281 13431620570327552695434961)
                  ·
                    refine ⟨10073715427745664521576221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13431620570327552695434961 10073715427745664521576221)
                    ·
                      refine ⟨3777643285404624195591083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10073715427745664521576221 3777643285404624195591083)
                      ·
                        rfl

theorem cell23_7356934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_7356934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356934 prefixEnd_7356934 := by exact prefixLift 7356934
  have htrace : WordTrace (prefixWord ++ tailWord_7356934) baseStart_7356934 baseEnd_7356934 := by
    simpa [prefixWord, tailWord_7356934, baseEnd_7356934] using wordTrace_append hprefix tailTrace_7356934
  have hstable : (prefixWord ++ tailWord_7356934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356934).length < 2 ^ (prefixWord ++ tailWord_7356934).sum := by decide
  have hdescent : baseEnd_7356934 < baseStart_7356934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356940 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 2, 3, 2]
def baseStart_7356940 : Nat := 118140960795 + 7356940 * 2 ^ 59
def prefixEnd_7356940 : Nat := 4983230072969 + 3 ^ 40 * 7356940 * 2
def baseEnd_7356940 : Nat := 3777646366288551172116055

theorem tailTrace_7356940 : CollatzResearch.WordTrace tailWord_7356940 prefixEnd_7356940 3777646366288551172116055 := by
  unfold tailWord_7356940
  simp only [CollatzResearch.WordTrace]
  refine ⟨134164822983535160082398137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178886430644713546776530849 134164822983535160082398137)
  ·
    refine ⟨100623617237651370061798603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134164822983535160082398137 100623617237651370061798603)
    ·
      refine ⟨150935425856477055092697905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100623617237651370061798603 150935425856477055092697905)
      ·
        refine ⟨113201569392357791319523429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150935425856477055092697905 113201569392357791319523429)
        ·
          refine ⟨21225294261067085872410643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113201569392357791319523429 21225294261067085872410643)
          ·
            refine ⟨31837941391600628808615965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21225294261067085872410643 31837941391600628808615965)
            ·
              refine ⟨11939228021850235803230987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31837941391600628808615965 11939228021850235803230987)
              ·
                refine ⟨17908842032775353704846481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11939228021850235803230987 17908842032775353704846481)
                ·
                  refine ⟨13431631524581515278634861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17908842032775353704846481 13431631524581515278634861)
                  ·
                    refine ⟨5036861821718068229488073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13431631524581515278634861 5036861821718068229488073)
                    ·
                      refine ⟨3777646366288551172116055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5036861821718068229488073 3777646366288551172116055)
                      ·
                        rfl

theorem cell23_7356940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_7356940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356940 prefixEnd_7356940 := by exact prefixLift 7356940
  have htrace : WordTrace (prefixWord ++ tailWord_7356940) baseStart_7356940 baseEnd_7356940 := by
    simpa [prefixWord, tailWord_7356940, baseEnd_7356940] using wordTrace_append hprefix tailTrace_7356940
  have hstable : (prefixWord ++ tailWord_7356940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356940).length < 2 ^ (prefixWord ++ tailWord_7356940).sum := by decide
  have hdescent : baseEnd_7356940 < baseStart_7356940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356963 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 4, 4]
def baseStart_7356963 : Nat := 118140960795 + 7356963 * 2 ^ 59
def prefixEnd_7356963 : Nat := 4983230072969 + 3 ^ 40 * 7356963 * 2
def baseEnd_7356963 : Nat := 1259219392114534860709483

theorem tailTrace_7356963 : CollatzResearch.WordTrace tailWord_7356963 prefixEnd_7356963 1259219392114534860709483 := by
  unfold tailWord_7356963
  simp only [CollatzResearch.WordTrace]
  refine ⟨268330484845986995092883543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178886989897324663395255695 268330484845986995092883543)
  ·
    refine ⟨402495727268980492639325315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268330484845986995092883543 402495727268980492639325315)
    ·
      refine ⟨603743590903470738958987973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402495727268980492639325315 603743590903470738958987973)
      ·
        refine ⟨113201923294400763554810245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 603743590903470738958987973 113201923294400763554810245)
        ·
          refine ⟨21225360617700143166526921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113201923294400763554810245 21225360617700143166526921)
          ·
            refine ⟨15919020463275107374895191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21225360617700143166526921 15919020463275107374895191)
            ·
              refine ⟨23878530694912661062342787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15919020463275107374895191 23878530694912661062342787)
              ·
                refine ⟨35817796042368991593514181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23878530694912661062342787 35817796042368991593514181)
                ·
                  refine ⟨6715836757944185923783909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35817796042368991593514181 6715836757944185923783909)
                  ·
                    refine ⟨1259219392114534860709483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6715836757944185923783909 1259219392114534860709483)
                    ·
                      rfl

theorem cell23_7356963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 4].length) (baseStart_7356963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356963 prefixEnd_7356963 := by exact prefixLift 7356963
  have htrace : WordTrace (prefixWord ++ tailWord_7356963) baseStart_7356963 baseEnd_7356963 := by
    simpa [prefixWord, tailWord_7356963, baseEnd_7356963] using wordTrace_append hprefix tailTrace_7356963
  have hstable : (prefixWord ++ tailWord_7356963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356963).length < 2 ^ (prefixWord ++ tailWord_7356963).sum := by decide
  have hdescent : baseEnd_7356963 < baseStart_7356963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356993 : List Nat := [1, 2, 5, 1, 1, 2, 4, 7]
def baseStart_7356993 : Nat := 118140960795 + 7356993 * 2 ^ 59
def prefixEnd_7356993 : Nat := 4983230072969 + 3 ^ 40 * 7356993 * 2
def baseEnd_7356993 : Nat := 139913836324564424620493

theorem tailTrace_7356993 : CollatzResearch.WordTrace tailWord_7356993 prefixEnd_7356993 139913836324564424620493 := by
  unfold tailWord_7356993
  simp only [CollatzResearch.WordTrace]
  refine ⟨268331579035878310216475633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178887719357252206810983755 268331579035878310216475633)
  ·
    refine ⟨201248684276908732662356725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268331579035878310216475633 201248684276908732662356725)
    ·
      refine ⟨18867064150960193687095943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201248684276908732662356725 18867064150960193687095943)
      ·
        refine ⟨28300596226440290530643915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18867064150960193687095943 28300596226440290530643915)
        ·
          refine ⟨42450894339660435795965873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28300596226440290530643915 42450894339660435795965873)
          ·
            refine ⟨31838170754745326846974405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42450894339660435795965873 31838170754745326846974405)
            ·
              refine ⟨5969657016514748783807701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31838170754745326846974405 5969657016514748783807701)
              ·
                refine ⟨139913836324564424620493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5969657016514748783807701 139913836324564424620493)
                ·
                  rfl

theorem cell23_7356993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 7].length) (baseStart_7356993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7356993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7356993 prefixEnd_7356993 := by exact prefixLift 7356993
  have htrace : WordTrace (prefixWord ++ tailWord_7356993) baseStart_7356993 baseEnd_7356993 := by
    simpa [prefixWord, tailWord_7356993, baseEnd_7356993] using wordTrace_append hprefix tailTrace_7356993
  have hstable : (prefixWord ++ tailWord_7356993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356993).length < 2 ^ (prefixWord ++ tailWord_7356993).sum := by decide
  have hdescent : baseEnd_7356993 < baseStart_7356993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357003 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 4, 1, 3]
def baseStart_7357003 : Nat := 118140960795 + 7357003 * 2 ^ 59
def prefixEnd_7357003 : Nat := 4983230072969 + 3 ^ 40 * 7357003 * 2
def baseEnd_7357003 : Nat := 3777678715569784425628265

theorem tailTrace_7357003 : CollatzResearch.WordTrace tailWord_7357003 prefixEnd_7357003 3777678715569784425628265 := by
  unfold tailWord_7357003
  simp only [CollatzResearch.WordTrace]
  refine ⟨268331943765842081924339663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178887962510561387949559775 268331943765842081924339663)
  ·
    refine ⟨402497915648763122886509495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268331943765842081924339663 402497915648763122886509495)
    ·
      refine ⟨603746873473144684329764243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402497915648763122886509495 603746873473144684329764243)
      ·
        refine ⟨905620310209717026494646365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603746873473144684329764243 905620310209717026494646365)
        ·
          refine ⟨339607616328643884935492387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 905620310209717026494646365 339607616328643884935492387)
          ·
            refine ⟨509411424492965827403238581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339607616328643884935492387 509411424492965827403238581)
            ·
              refine ⟨47757321046215546319053617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 509411424492965827403238581 47757321046215546319053617)
              ·
                refine ⟨35817990784661659739290213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47757321046215546319053617 35817990784661659739290213)
                ·
                  refine ⟨6715873272124061201116915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35817990784661659739290213 6715873272124061201116915)
                  ·
                    refine ⟨10073809908186091801675373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6715873272124061201116915 10073809908186091801675373)
                    ·
                      refine ⟨3777678715569784425628265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10073809908186091801675373 3777678715569784425628265)
                      ·
                        rfl

theorem cell23_7357003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 1, 3].length) (baseStart_7357003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357003 prefixEnd_7357003 := by exact prefixLift 7357003
  have htrace : WordTrace (prefixWord ++ tailWord_7357003) baseStart_7357003 baseEnd_7357003 := by
    simpa [prefixWord, tailWord_7357003, baseEnd_7357003] using wordTrace_append hprefix tailTrace_7357003
  have hstable : (prefixWord ++ tailWord_7357003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357003).length < 2 ^ (prefixWord ++ tailWord_7357003).sum := by decide
  have hdescent : baseEnd_7357003 < baseStart_7357003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357036 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 2, 6]
def baseStart_7357036 : Nat := 118140960795 + 7357036 * 2 ^ 59
def prefixEnd_7357036 : Nat := 4983230072969 + 3 ^ 40 * 7357036 * 2
def baseEnd_7357036 : Nat := 1259231886810460932171871

theorem tailTrace_7357036 : CollatzResearch.WordTrace tailWord_7357036 prefixEnd_7357036 1259231886810460932171871 := by
  unfold tailWord_7357036
  simp only [CollatzResearch.WordTrace]
  refine ⟨134166573687361264280145481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178888764916481685706860641 134166573687361264280145481)
  ·
    refine ⟨100624930265520948210109111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134166573687361264280145481 100624930265520948210109111)
    ·
      refine ⟨150937395398281422315163667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100624930265520948210109111 150937395398281422315163667)
      ·
        refine ⟨226406093097422133472745501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150937395398281422315163667 226406093097422133472745501)
        ·
          refine ⟨84902284911533300052279563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226406093097422133472745501 84902284911533300052279563)
          ·
            refine ⟨127353427367299950078419345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84902284911533300052279563 127353427367299950078419345)
            ·
              refine ⟨95515070525474962558814509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127353427367299950078419345 95515070525474962558814509)
              ·
                refine ⟨35818151447053110959555441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95515070525474962558814509 35818151447053110959555441)
                ·
                  refine ⟨26863613585289833219666581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35818151447053110959555441 26863613585289833219666581)
                  ·
                    refine ⟨1259231886810460932171871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26863613585289833219666581 1259231886810460932171871)
                    ·
                      rfl

theorem cell23_7357036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_7357036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357036 prefixEnd_7357036 := by exact prefixLift 7357036
  have htrace : WordTrace (prefixWord ++ tailWord_7357036) baseStart_7357036 baseEnd_7357036 := by
    simpa [prefixWord, tailWord_7357036, baseEnd_7357036] using wordTrace_append hprefix tailTrace_7357036
  have hstable : (prefixWord ++ tailWord_7357036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357036).length < 2 ^ (prefixWord ++ tailWord_7357036).sum := by decide
  have hdescent : baseEnd_7357036 < baseStart_7357036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357037 : List Nat := [1, 5, 1, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_7357037 : Nat := 118140960795 + 7357037 * 2 ^ 59
def prefixEnd_7357037 : Nat := 4983230072969 + 3 ^ 40 * 7357037 * 2
def baseEnd_7357037 : Nat := 3777696173912037292603109

theorem tailTrace_7357037 : CollatzResearch.WordTrace tailWord_7357037 prefixEnd_7357037 3777696173912037292603109 := by
  unfold tailWord_7357037
  simp only [CollatzResearch.WordTrace]
  refine ⟨268333183847718905731077365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178888789231812603820718243 268333183847718905731077365)
  ·
    refine ⟨25156235985723647412288503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268333183847718905731077365 25156235985723647412288503)
    ·
      refine ⟨37734353978585471118432755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25156235985723647412288503 37734353978585471118432755)
      ·
        refine ⟨56601530967878206677649133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37734353978585471118432755 56601530967878206677649133)
        ·
          refine ⟨21225574112954327504118425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56601530967878206677649133 21225574112954327504118425)
          ·
            refine ⟨15919180584715745628088819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21225574112954327504118425 15919180584715745628088819)
            ·
              refine ⟨23878770877073618442133229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15919180584715745628088819 23878770877073618442133229)
              ·
                refine ⟨8954539078902606915799961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23878770877073618442133229 8954539078902606915799961)
                ·
                  refine ⟨6715904309176955186849971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8954539078902606915799961 6715904309176955186849971)
                  ·
                    refine ⟨10073856463765432780274957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6715904309176955186849971 10073856463765432780274957)
                    ·
                      refine ⟨3777696173912037292603109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10073856463765432780274957 3777696173912037292603109)
                      ·
                        rfl

theorem cell23_7357037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_7357037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357037 prefixEnd_7357037 := by exact prefixLift 7357037
  have htrace : WordTrace (prefixWord ++ tailWord_7357037) baseStart_7357037 baseEnd_7357037 := by
    simpa [prefixWord, tailWord_7357037, baseEnd_7357037] using wordTrace_append hprefix tailTrace_7357037
  have hstable : (prefixWord ++ tailWord_7357037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357037).length < 2 ^ (prefixWord ++ tailWord_7357037).sum := by decide
  have hdescent : baseEnd_7357037 < baseStart_7357037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357058 : List Nat := [3, 4, 3, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7357058 : Nat := 118140960795 + 7357058 * 2 ^ 59
def prefixEnd_7357058 : Nat := 4983230072969 + 3 ^ 40 * 7357058 * 2
def baseEnd_7357058 : Nat := 3777706957005781710440513

theorem tailTrace_7357058 : CollatzResearch.WordTrace tailWord_7357058 prefixEnd_7357058 3777706957005781710440513 := by
  unfold tailWord_7357058
  simp only [CollatzResearch.WordTrace]
  refine ⟨67083487445160706579397957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178889299853761884211727885 67083487445160706579397957)
  ·
    refine ⟨12578153895967632483637117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67083487445160706579397957 12578153895967632483637117)
    ·
      refine ⟨4716807710987862181363919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12578153895967632483637117 4716807710987862181363919)
      ·
        refine ⟨7075211566481793272045879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4716807710987862181363919 7075211566481793272045879)
        ·
          refine ⟨10612817349722689908068819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7075211566481793272045879 10612817349722689908068819)
          ·
            refine ⟨15919226024584034862103229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10612817349722689908068819 15919226024584034862103229)
            ·
              refine ⟨5969709759219013073288711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15919226024584034862103229 5969709759219013073288711)
              ·
                refine ⟨8954564638828519609933067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5969709759219013073288711 8954564638828519609933067)
                ·
                  refine ⟨13431846958242779414899601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8954564638828519609933067 13431846958242779414899601)
                  ·
                    refine ⟨10073885218682084561174701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13431846958242779414899601 10073885218682084561174701)
                    ·
                      refine ⟨3777706957005781710440513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10073885218682084561174701 3777706957005781710440513)
                      ·
                        rfl

theorem cell23_7357058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7357058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357058 prefixEnd_7357058 := by exact prefixLift 7357058
  have htrace : WordTrace (prefixWord ++ tailWord_7357058) baseStart_7357058 baseEnd_7357058 := by
    simpa [prefixWord, tailWord_7357058, baseEnd_7357058] using wordTrace_append hprefix tailTrace_7357058
  have hstable : (prefixWord ++ tailWord_7357058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357058).length < 2 ^ (prefixWord ++ tailWord_7357058).sum := by decide
  have hdescent : baseEnd_7357058 < baseStart_7357058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357060 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_7357060 : Nat := 118140960795 + 7357060 * 2 ^ 59
def prefixEnd_7357060 : Nat := 4983230072969 + 3 ^ 40 * 7357060 * 2
def baseEnd_7357060 : Nat := 3777707983967090702615503

theorem tailTrace_7357060 : CollatzResearch.WordTrace tailWord_7357060 prefixEnd_7357060 3777707983967090702615503 := by
  unfold tailWord_7357060
  simp only [CollatzResearch.WordTrace]
  refine ⟨134167011363317790329582317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178889348484423720439443089 134167011363317790329582317)
  ·
    refine ⟨50312629261244171373593369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134167011363317790329582317 50312629261244171373593369)
    ·
      refine ⟨37734471945933128530195027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50312629261244171373593369 37734471945933128530195027)
      ·
        refine ⟨56601707918899692795292541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37734471945933128530195027 56601707918899692795292541)
        ·
          refine ⟨21225640469587384798234703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56601707918899692795292541 21225640469587384798234703)
          ·
            refine ⟨31838460704381077197352055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21225640469587384798234703 31838460704381077197352055)
            ·
              refine ⟨47757691056571615796028083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31838460704381077197352055 47757691056571615796028083)
              ·
                refine ⟨71636536584857423694042125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47757691056571615796028083 71636536584857423694042125)
                ·
                  refine ⟨26863701219321533885265797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71636536584857423694042125 26863701219321533885265797)
                  ·
                    refine ⟨5036943978622787603487337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26863701219321533885265797 5036943978622787603487337)
                    ·
                      refine ⟨3777707983967090702615503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5036943978622787603487337 3777707983967090702615503)
                      ·
                        rfl

theorem cell23_7357060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_7357060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357060 prefixEnd_7357060 := by exact prefixLift 7357060
  have htrace : WordTrace (prefixWord ++ tailWord_7357060) baseStart_7357060 baseEnd_7357060 := by
    simpa [prefixWord, tailWord_7357060, baseEnd_7357060] using wordTrace_append hprefix tailTrace_7357060
  have hstable : (prefixWord ++ tailWord_7357060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357060).length < 2 ^ (prefixWord ++ tailWord_7357060).sum := by decide
  have hdescent : baseEnd_7357060 < baseStart_7357060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357170 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_7357170 : Nat := 118140960795 + 7357170 * 2 ^ 59
def prefixEnd_7357170 : Nat := 4983230072969 + 3 ^ 40 * 7357170 * 2
def baseEnd_7357170 : Nat := 3777764466839085272239997

theorem tailTrace_7357170 : CollatzResearch.WordTrace tailWord_7357170 prefixEnd_7357170 3777764466839085272239997 := by
  unfold tailWord_7357170
  simp only [CollatzResearch.WordTrace]
  refine ⟨67084508689059267361417241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178892023170824712963779309 67084508689059267361417241)
  ·
    refine ⟨50313381516794450521062931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67084508689059267361417241 50313381516794450521062931)
    ·
      refine ⟨75470072275191675781594397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50313381516794450521062931 75470072275191675781594397)
      ·
        refine ⟨28301277103196878418097899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75470072275191675781594397 28301277103196878418097899)
        ·
          refine ⟨42451915654795317627146849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28301277103196878418097899 42451915654795317627146849)
          ·
            refine ⟨31838936741096488220360137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42451915654795317627146849 31838936741096488220360137)
            ·
              refine ⟨23879202555822366165270103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31838936741096488220360137 23879202555822366165270103)
              ·
                refine ⟨35818803833733549247905155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23879202555822366165270103 35818803833733549247905155)
                ·
                  refine ⟨53728205750600323871857733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35818803833733549247905155 53728205750600323871857733)
                  ·
                    refine ⟨10074038578237560725973325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53728205750600323871857733 10074038578237560725973325)
                    ·
                      refine ⟨3777764466839085272239997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10074038578237560725973325 3777764466839085272239997)
                      ·
                        rfl

theorem cell23_7357170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_7357170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357170 prefixEnd_7357170 := by exact prefixLift 7357170
  have htrace : WordTrace (prefixWord ++ tailWord_7357170) baseStart_7357170 baseEnd_7357170 := by
    simpa [prefixWord, tailWord_7357170, baseEnd_7357170] using wordTrace_append hprefix tailTrace_7357170
  have hstable : (prefixWord ++ tailWord_7357170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357170).length < 2 ^ (prefixWord ++ tailWord_7357170).sum := by decide
  have hdescent : baseEnd_7357170 < baseStart_7357170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357194 : List Nat := [3, 1, 2, 2, 1, 2, 5, 2, 1, 4]
def baseStart_7357194 : Nat := 118140960795 + 7357194 * 2 ^ 59
def prefixEnd_7357194 : Nat := 4983230072969 + 3 ^ 40 * 7357194 * 2
def baseEnd_7357194 : Nat := 1259258930124931059446629

theorem tailTrace_7357194 : CollatzResearch.WordTrace tailWord_7357194 prefixEnd_7357194 1259258930124931059446629 := by
  unfold tailWord_7357194
  simp only [CollatzResearch.WordTrace]
  refine ⟨67084727527037530386135659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178892606738766747696361757 67084727527037530386135659)
  ·
    refine ⟨100627091290556295579203489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67084727527037530386135659 100627091290556295579203489)
    ·
      refine ⟨75470318467917221684402617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100627091290556295579203489 75470318467917221684402617)
      ·
        refine ⟨56602738850937916263301963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75470318467917221684402617 56602738850937916263301963)
        ·
          refine ⟨84904108276406874394952945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56602738850937916263301963 84904108276406874394952945)
          ·
            refine ⟨63678081207305155796214709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84904108276406874394952945 63678081207305155796214709)
            ·
              refine ⟨5969820113184858355895129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63678081207305155796214709 5969820113184858355895129)
              ·
                refine ⟨4477365084888643766921347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5969820113184858355895129 4477365084888643766921347)
                ·
                  refine ⟨6716047627332965650382021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4477365084888643766921347 6716047627332965650382021)
                  ·
                    refine ⟨1259258930124931059446629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6716047627332965650382021 1259258930124931059446629)
                    ·
                      rfl

theorem cell23_7357194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_7357194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357194 prefixEnd_7357194 := by exact prefixLift 7357194
  have htrace : WordTrace (prefixWord ++ tailWord_7357194) baseStart_7357194 baseEnd_7357194 := by
    simpa [prefixWord, tailWord_7357194, baseEnd_7357194] using wordTrace_append hprefix tailTrace_7357194
  have hstable : (prefixWord ++ tailWord_7357194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357194).length < 2 ^ (prefixWord ++ tailWord_7357194).sum := by decide
  have hdescent : baseEnd_7357194 < baseStart_7357194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357203 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 3, 5]
def baseStart_7357203 : Nat := 118140960795 + 7357203 * 2 ^ 59
def prefixEnd_7357203 : Nat := 4983230072969 + 3 ^ 40 * 7357203 * 2
def baseEnd_7357203 : Nat := 1259260470566894547709115

theorem tailTrace_7357203 : CollatzResearch.WordTrace tailWord_7357203 prefixEnd_7357203 1259260470566894547709115 := by
  unfold tailWord_7357203
  simp only [CollatzResearch.WordTrace]
  refine ⟨268339238365117516081620263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178892825576745010721080175 268339238365117516081620263)
  ·
    refine ⟨402508857547676274122430395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268339238365117516081620263 402508857547676274122430395)
    ·
      refine ⟨603763286321514411183645593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402508857547676274122430395 603763286321514411183645593)
      ·
        refine ⟨452822464741135808387734195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 603763286321514411183645593 452822464741135808387734195)
        ·
          refine ⟨679233697111703712581601293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452822464741135808387734195 679233697111703712581601293)
          ·
            refine ⟨254712636416888892218100485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 679233697111703712581601293 254712636416888892218100485)
            ·
              refine ⟨47758619328166667290893841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254712636416888892218100485 47758619328166667290893841)
              ·
                refine ⟨35818964496125000468170381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47758619328166667290893841 35818964496125000468170381)
                ·
                  refine ⟨13432111686046875175563893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35818964496125000468170381 13432111686046875175563893)
                  ·
                    refine ⟨1259260470566894547709115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13432111686046875175563893 1259260470566894547709115)
                    ·
                      rfl

theorem cell23_7357203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 5].length) (baseStart_7357203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357203 prefixEnd_7357203 := by exact prefixLift 7357203
  have htrace : WordTrace (prefixWord ++ tailWord_7357203) baseStart_7357203 baseEnd_7357203 := by
    simpa [prefixWord, tailWord_7357203, baseEnd_7357203] using wordTrace_append hprefix tailTrace_7357203
  have hstable : (prefixWord ++ tailWord_7357203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357203).length < 2 ^ (prefixWord ++ tailWord_7357203).sum := by decide
  have hdescent : baseEnd_7357203 < baseStart_7357203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357234 : List Nat := [3, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3]
def baseStart_7357234 : Nat := 118140960795 + 7357234 * 2 ^ 59
def prefixEnd_7357234 : Nat := 4983230072969 + 3 ^ 40 * 7357234 * 2
def baseEnd_7357234 : Nat := 3777797329600973021839703

theorem tailTrace_7357234 : CollatzResearch.WordTrace tailWord_7357234 prefixEnd_7357234 3777797329600973021839703 := by
  unfold tailWord_7357234
  simp only [CollatzResearch.WordTrace]
  refine ⟨67085092257001302093999689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178893579352003472250665837 67085092257001302093999689)
  ·
    refine ⟨50313819192750976570499767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67085092257001302093999689 50313819192750976570499767)
    ·
      refine ⟨75470728789126464855749651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50313819192750976570499767 75470728789126464855749651)
      ·
        refine ⟨113206093183689697283624477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75470728789126464855749651 113206093183689697283624477)
        ·
          refine ⟨42452284943883636481359179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113206093183689697283624477 42452284943883636481359179)
          ·
            refine ⟨63678427415825454722038769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42452284943883636481359179 63678427415825454722038769)
            ·
              refine ⟨47758820561869091041529077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63678427415825454722038769 47758820561869091041529077)
              ·
                refine ⟨4477389427675227285143351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47758820561869091041529077 4477389427675227285143351)
                ·
                  refine ⟨6716084141512840927715027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4477389427675227285143351 6716084141512840927715027)
                  ·
                    refine ⟨10074126212269261391572541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6716084141512840927715027 10074126212269261391572541)
                    ·
                      refine ⟨3777797329600973021839703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10074126212269261391572541 3777797329600973021839703)
                      ·
                        rfl

theorem cell23_7357234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_7357234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357234 prefixEnd_7357234 := by exact prefixLift 7357234
  have htrace : WordTrace (prefixWord ++ tailWord_7357234) baseStart_7357234 baseEnd_7357234 := by
    simpa [prefixWord, tailWord_7357234, baseEnd_7357234] using wordTrace_append hprefix tailTrace_7357234
  have hstable : (prefixWord ++ tailWord_7357234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357234).length < 2 ^ (prefixWord ++ tailWord_7357234).sum := by decide
  have hdescent : baseEnd_7357234 < baseStart_7357234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357253 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_7357253 : Nat := 118140960795 + 7357253 * 2 ^ 59
def prefixEnd_7357253 : Nat := 4983230072969 + 3 ^ 40 * 7357253 * 2
def baseEnd_7357253 : Nat := 3777807085733408447502115

theorem tailTrace_7357253 : CollatzResearch.WordTrace tailWord_7357253 prefixEnd_7357253 3777807085733408447502115 := by
  unfold tailWord_7357253
  simp only [CollatzResearch.WordTrace]
  refine ⟨268341062014936374620940413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178894041343290916413960275 268341062014936374620940413)
  ·
    refine ⟨100627898255601140482852655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268341062014936374620940413 100627898255601140482852655)
    ·
      refine ⟨150941847383401710724278983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100627898255601140482852655 150941847383401710724278983)
      ·
        refine ⟨226412771075102566086418475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150941847383401710724278983 226412771075102566086418475)
        ·
          refine ⟨339619156612653849129627713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226412771075102566086418475 339619156612653849129627713)
          ·
            refine ⟨254714367459490386847220785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339619156612653849129627713 254714367459490386847220785)
            ·
              refine ⟨191035775594617790135415589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254714367459490386847220785 191035775594617790135415589)
              ·
                refine ⟨35819207923990835650390423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191035775594617790135415589 35819207923990835650390423)
                ·
                  refine ⟨53728811885986253475585635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35819207923990835650390423 53728811885986253475585635)
                  ·
                    refine ⟨80593217828979380213378453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53728811885986253475585635 80593217828979380213378453)
                    ·
                      refine ⟨3777807085733408447502115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80593217828979380213378453 3777807085733408447502115)
                      ·
                        rfl

theorem cell23_7357253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_7357253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357253 prefixEnd_7357253 := by exact prefixLift 7357253
  have htrace : WordTrace (prefixWord ++ tailWord_7357253) baseStart_7357253 baseEnd_7357253 := by
    simpa [prefixWord, tailWord_7357253, baseEnd_7357253] using wordTrace_append hprefix tailTrace_7357253
  have hstable : (prefixWord ++ tailWord_7357253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357253).length < 2 ^ (prefixWord ++ tailWord_7357253).sum := by decide
  have hdescent : baseEnd_7357253 < baseStart_7357253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357274 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2]
def baseStart_7357274 : Nat := 118140960795 + 7357274 * 2 ^ 59
def prefixEnd_7357274 : Nat := 4983230072969 + 3 ^ 40 * 7357274 * 2
def baseEnd_7357274 : Nat := 3777817868827152865339519

theorem tailTrace_7357274 : CollatzResearch.WordTrace tailWord_7357274 prefixEnd_7357274 3777817868827152865339519 := by
  unfold tailWord_7357274
  simp only [CollatzResearch.WordTrace]
  refine ⟨67085456986965073801863719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178894551965240196804969917 67085456986965073801863719)
  ·
    refine ⟨100628185480447610702795579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67085456986965073801863719 100628185480447610702795579)
    ·
      refine ⟨150942278220671416054193369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100628185480447610702795579 150942278220671416054193369)
      ·
        refine ⟨113206708665503562040645027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150942278220671416054193369 113206708665503562040645027)
        ·
          refine ⟨169810062998255343060967541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113206708665503562040645027 169810062998255343060967541)
          ·
            refine ⟨15919693406086438411965707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169810062998255343060967541 15919693406086438411965707)
            ·
              refine ⟨23879540109129657617948561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15919693406086438411965707 23879540109129657617948561)
              ·
                refine ⟨17909655081847243213461421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23879540109129657617948561 17909655081847243213461421)
                ·
                  refine ⟨6716120655692716205048033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17909655081847243213461421 6716120655692716205048033)
                  ·
                    refine ⟨5037090491769537153786025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6716120655692716205048033 5037090491769537153786025)
                    ·
                      refine ⟨3777817868827152865339519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5037090491769537153786025 3777817868827152865339519)
                      ·
                        rfl

theorem cell23_7357274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_7357274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357274 prefixEnd_7357274 := by exact prefixLift 7357274
  have htrace : WordTrace (prefixWord ++ tailWord_7357274) baseStart_7357274 baseEnd_7357274 := by
    simpa [prefixWord, tailWord_7357274, baseEnd_7357274] using wordTrace_append hprefix tailTrace_7357274
  have hstable : (prefixWord ++ tailWord_7357274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357274).length < 2 ^ (prefixWord ++ tailWord_7357274).sum := by decide
  have hdescent : baseEnd_7357274 < baseStart_7357274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357280 : List Nat := [2, 1, 1, 3, 3, 1, 5, 7]
def baseStart_7357280 : Nat := 118140960795 + 7357280 * 2 ^ 59
def prefixEnd_7357280 : Nat := 4983230072969 + 3 ^ 40 * 7357280 * 2
def baseEnd_7357280 : Nat := 139919294433743697846833

theorem tailTrace_7357280 : CollatzResearch.WordTrace tailWord_7357280 prefixEnd_7357280 139919294433743697846833 := by
  unfold tailWord_7357280
  simp only [CollatzResearch.WordTrace]
  refine ⟨134171023392919279116086647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178894697857225705488115529 134171023392919279116086647)
  ·
    refine ⟨201256535089378918674129971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134171023392919279116086647 201256535089378918674129971)
    ·
      refine ⟨301884802634068378011194957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201256535089378918674129971 301884802634068378011194957)
      ·
        refine ⟨113206800987775641754198109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301884802634068378011194957 113206800987775641754198109)
        ·
          refine ⟨42452550370415865657824291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113206800987775641754198109 42452550370415865657824291)
          ·
            refine ⟨63678825555623798486736437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42452550370415865657824291 63678825555623798486736437)
            ·
              refine ⟨5969889895839731108131541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63678825555623798486736437 5969889895839731108131541)
              ·
                refine ⟨139919294433743697846833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5969889895839731108131541 139919294433743697846833)
                ·
                  rfl

theorem cell23_7357280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 7].length) (baseStart_7357280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357280 prefixEnd_7357280 := by exact prefixLift 7357280
  have htrace : WordTrace (prefixWord ++ tailWord_7357280) baseStart_7357280 baseEnd_7357280 := by
    simpa [prefixWord, tailWord_7357280, baseEnd_7357280] using wordTrace_append hprefix tailTrace_7357280
  have hstable : (prefixWord ++ tailWord_7357280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357280).length < 2 ^ (prefixWord ++ tailWord_7357280).sum := by decide
  have hdescent : baseEnd_7357280 < baseStart_7357280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357347 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 1, 4, 2]
def baseStart_7357347 : Nat := 118140960795 + 7357347 * 2 ^ 59
def prefixEnd_7357347 : Nat := 4983230072969 + 3 ^ 40 * 7357347 * 2
def baseEnd_7357347 : Nat := 3777855352914931079726683

theorem tailTrace_7357347 : CollatzResearch.WordTrace tailWord_7357347 prefixEnd_7357347 3777855352914931079726683 := by
  unfold tailWord_7357347
  simp only [CollatzResearch.WordTrace]
  refine ⟨268344490476595828674862295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178896326984397219116574863 268344490476595828674862295)
  ·
    refine ⟨402516735714893743012293443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268344490476595828674862295 402516735714893743012293443)
    ·
      refine ⟨603775103572340614518440165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402516735714893743012293443 603775103572340614518440165)
      ·
        refine ⟨113207831919813865222207531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 603775103572340614518440165 113207831919813865222207531)
        ·
          refine ⟨169811747879720797833311297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113207831919813865222207531 169811747879720797833311297)
          ·
            refine ⟨127358810909790598374983473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169811747879720797833311297 127358810909790598374983473)
            ·
              refine ⟨95519108182342948781237605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127358810909790598374983473 95519108182342948781237605)
              ·
                refine ⟨17909832784189302896482051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95519108182342948781237605 17909832784189302896482051)
                ·
                  refine ⟨26864749176283954344723077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17909832784189302896482051 26864749176283954344723077)
                  ·
                    refine ⟨5037140470553241439635577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26864749176283954344723077 5037140470553241439635577)
                    ·
                      refine ⟨3777855352914931079726683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5037140470553241439635577 3777855352914931079726683)
                      ·
                        rfl

theorem cell23_7357347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_7357347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357347 prefixEnd_7357347 := by exact prefixLift 7357347
  have htrace : WordTrace (prefixWord ++ tailWord_7357347) baseStart_7357347 baseEnd_7357347 := by
    simpa [prefixWord, tailWord_7357347, baseEnd_7357347] using wordTrace_append hprefix tailTrace_7357347
  have hstable : (prefixWord ++ tailWord_7357347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357347).length < 2 ^ (prefixWord ++ tailWord_7357347).sum := by decide
  have hdescent : baseEnd_7357347 < baseStart_7357347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357420 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_7357420 : Nat := 118140960795 + 7357420 * 2 ^ 59
def prefixEnd_7357420 : Nat := 4983230072969 + 3 ^ 40 * 7357420 * 2
def baseEnd_7357420 : Nat := 3777892837002709294113847

theorem tailTrace_7357420 : CollatzResearch.WordTrace tailWord_7357420 prefixEnd_7357420 3777892837002709294113847 := by
  unfold tailWord_7357420
  simp only [CollatzResearch.WordTrace]
  refine ⟨134173576502665681071134857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178898102003554241428179809 134173576502665681071134857)
  ·
    refine ⟨100630182376999260803351143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134173576502665681071134857 100630182376999260803351143)
    ·
      refine ⟨150945273565498891205026715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100630182376999260803351143 150945273565498891205026715)
      ·
        refine ⟨226417910348248336807540073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150945273565498891205026715 226417910348248336807540073)
        ·
          refine ⟨169813432761186252605655055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226417910348248336807540073 169813432761186252605655055)
          ·
            refine ⟨254720149141779378908482583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169813432761186252605655055 254720149141779378908482583)
            ·
              refine ⟨382080223712669068362723875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254720149141779378908482583 382080223712669068362723875)
              ·
                refine ⟨573120335569003602544085813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382080223712669068362723875 573120335569003602544085813)
                ·
                  refine ⟨53730031459594087738508045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 573120335569003602544085813 53730031459594087738508045)
                  ·
                    refine ⟨20148761797347782901940517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53730031459594087738508045 20148761797347782901940517)
                    ·
                      refine ⟨3777892837002709294113847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20148761797347782901940517 3777892837002709294113847)
                      ·
                        rfl

theorem cell23_7357420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_7357420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357420 prefixEnd_7357420 := by exact prefixLift 7357420
  have htrace : WordTrace (prefixWord ++ tailWord_7357420) baseStart_7357420 baseEnd_7357420 := by
    simpa [prefixWord, tailWord_7357420, baseEnd_7357420] using wordTrace_append hprefix tailTrace_7357420
  have hstable : (prefixWord ++ tailWord_7357420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357420).length < 2 ^ (prefixWord ++ tailWord_7357420).sum := by decide
  have hdescent : baseEnd_7357420 < baseStart_7357420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357454 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_7357454 : Nat := 118140960795 + 7357454 * 2 ^ 59
def prefixEnd_7357454 : Nat := 4983230072969 + 3 ^ 40 * 7357454 * 2
def baseEnd_7357454 : Nat := 3777910295344962161088691

theorem tailTrace_7357454 : CollatzResearch.WordTrace tailWord_7357454 prefixEnd_7357454 3777910295344962161088691 := by
  unfold tailWord_7357454
  simp only [CollatzResearch.WordTrace]
  refine ⟨33543549135901023243625927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178898928724805457299338277 33543549135901023243625927)
  ·
    refine ⟨50315323703851534865438891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33543549135901023243625927 50315323703851534865438891)
    ·
      refine ⟨75472985555777302298158337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50315323703851534865438891 75472985555777302298158337)
      ·
        refine ⟨56604739166832976723618753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75472985555777302298158337 56604739166832976723618753)
        ·
          refine ⟨42453554375124732542714065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56604739166832976723618753 42453554375124732542714065)
          ·
            refine ⟨31840165781343549407035549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42453554375124732542714065 31840165781343549407035549)
            ·
              refine ⟨11940062168003831027638331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31840165781343549407035549 11940062168003831027638331)
              ·
                refine ⟨17910093252005746541457497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11940062168003831027638331 17910093252005746541457497)
                ·
                  refine ⟨13432569939004309906093123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17910093252005746541457497 13432569939004309906093123)
                  ·
                    refine ⟨20148854908506464859139685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13432569939004309906093123 20148854908506464859139685)
                    ·
                      refine ⟨3777910295344962161088691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20148854908506464859139685 3777910295344962161088691)
                      ·
                        rfl

theorem cell23_7357454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_7357454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357454 prefixEnd_7357454 := by exact prefixLift 7357454
  have htrace : WordTrace (prefixWord ++ tailWord_7357454) baseStart_7357454 baseEnd_7357454 := by
    simpa [prefixWord, tailWord_7357454, baseEnd_7357454] using wordTrace_append hprefix tailTrace_7357454
  have hstable : (prefixWord ++ tailWord_7357454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357454).length < 2 ^ (prefixWord ++ tailWord_7357454).sum := by decide
  have hdescent : baseEnd_7357454 < baseStart_7357454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357504 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 3, 1, 3]
def baseStart_7357504 : Nat := 118140960795 + 7357504 * 2 ^ 59
def prefixEnd_7357504 : Nat := 4983230072969 + 3 ^ 40 * 7357504 * 2
def baseEnd_7357504 : Nat := 3777935969377686965463461

theorem tailTrace_7357504 : CollatzResearch.WordTrace tailWord_7357504 prefixEnd_7357504 3777935969377686965463461 := by
  unfold tailWord_7357504
  simp only [CollatzResearch.WordTrace]
  refine ⟨134175108368513522244163783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178900144491351362992218377 134175108368513522244163783)
  ·
    refine ⟨201262662552770283366245675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134175108368513522244163783 201262662552770283366245675)
    ·
      refine ⟨301893993829155425049368513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201262662552770283366245675 301893993829155425049368513)
      ·
        refine ⟨226420495371866568787026385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301893993829155425049368513 226420495371866568787026385)
        ·
          refine ⟨169815371528899926590269789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226420495371866568787026385 169815371528899926590269789)
          ·
            refine ⟨63680764323337472471351171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169815371528899926590269789 63680764323337472471351171)
            ·
              refine ⟨95521146485006208707026757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63680764323337472471351171 95521146485006208707026757)
              ·
                refine ⟨17910214965938664132567517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95521146485006208707026757 17910214965938664132567517)
                ·
                  refine ⟨6716330612226999049712819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17910214965938664132567517 6716330612226999049712819)
                  ·
                    refine ⟨10074495918340498574569229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6716330612226999049712819 10074495918340498574569229)
                    ·
                      refine ⟨3777935969377686965463461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10074495918340498574569229 3777935969377686965463461)
                      ·
                        rfl

theorem cell23_7357504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_7357504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357504 prefixEnd_7357504 := by exact prefixLift 7357504
  have htrace : WordTrace (prefixWord ++ tailWord_7357504) baseStart_7357504 baseEnd_7357504 := by
    simpa [prefixWord, tailWord_7357504, baseEnd_7357504] using wordTrace_append hprefix tailTrace_7357504
  have hstable : (prefixWord ++ tailWord_7357504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357504).length < 2 ^ (prefixWord ++ tailWord_7357504).sum := by decide
  have hdescent : baseEnd_7357504 < baseStart_7357504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357514 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 1, 5, 2]
def baseStart_7357514 : Nat := 118140960795 + 7357514 * 2 ^ 59
def prefixEnd_7357514 : Nat := 4983230072969 + 3 ^ 40 * 7357514 * 2
def baseEnd_7357514 : Nat := 3777941104184231926338415

theorem tailTrace_7357514 : CollatzResearch.WordTrace tailWord_7357514 prefixEnd_7357514 3777941104184231926338415 := by
  unfold tailWord_7357514
  simp only [CollatzResearch.WordTrace]
  refine ⟨67087645366747704049047899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178900387644660544130794397 67087645366747704049047899)
  ·
    refine ⟨100631468050121556073571849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67087645366747704049047899 100631468050121556073571849)
    ·
      refine ⟨75473601037591167055178887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100631468050121556073571849 75473601037591167055178887)
      ·
        refine ⟨113210401556386750582768331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75473601037591167055178887 113210401556386750582768331)
        ·
          refine ⟨169815602334580125874152497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113210401556386750582768331 169815602334580125874152497)
          ·
            refine ⟨127361701750935094405614373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169815602334580125874152497 127361701750935094405614373)
            ·
              refine ⟨23880319078300330201052695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127361701750935094405614373 23880319078300330201052695)
              ·
                refine ⟨35820478617450495301579043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23880319078300330201052695 35820478617450495301579043)
                ·
                  refine ⟨53730717926175742952368565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35820478617450495301579043 53730717926175742952368565)
                  ·
                    refine ⟨5037254805578975901784553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53730717926175742952368565 5037254805578975901784553)
                    ·
                      refine ⟨3777941104184231926338415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5037254805578975901784553 3777941104184231926338415)
                      ·
                        rfl

theorem cell23_7357514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_7357514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357514 prefixEnd_7357514 := by exact prefixLift 7357514
  have htrace : WordTrace (prefixWord ++ tailWord_7357514) baseStart_7357514 baseEnd_7357514 := by
    simpa [prefixWord, tailWord_7357514, baseEnd_7357514] using wordTrace_append hprefix tailTrace_7357514
  have hstable : (prefixWord ++ tailWord_7357514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357514).length < 2 ^ (prefixWord ++ tailWord_7357514).sum := by decide
  have hdescent : baseEnd_7357514 < baseStart_7357514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357524 : List Nat := [2, 4, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_7357524 : Nat := 118140960795 + 7357524 * 2 ^ 59
def prefixEnd_7357524 : Nat := 4983230072969 + 3 ^ 40 * 7357524 * 2
def baseEnd_7357524 : Nat := 1259315412996925629071123

theorem tailTrace_7357524 : CollatzResearch.WordTrace tailWord_7357524 prefixEnd_7357524 1259315412996925629071123 := by
  unfold tailWord_7357524
  simp only [CollatzResearch.WordTrace]
  refine ⟨134175473098477293952027813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178900630797969725269370417 134175473098477293952027813)
  ·
    refine ⟨25157901205964492616005215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134175473098477293952027813 25157901205964492616005215)
    ·
      refine ⟨37736851808946738924007823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25157901205964492616005215 37736851808946738924007823)
      ·
        refine ⟨56605277713420108386011735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37736851808946738924007823 56605277713420108386011735)
        ·
          refine ⟨84907916570130162579017603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56605277713420108386011735 84907916570130162579017603)
          ·
            refine ⟨127361874855195243868526405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84907916570130162579017603 127361874855195243868526405)
            ·
              refine ⟨23880351535349108225348701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127361874855195243868526405 23880351535349108225348701)
              ·
                refine ⟨8955131825755915584505763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23880351535349108225348701 8955131825755915584505763)
                ·
                  refine ⟨13432697738633873376758645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8955131825755915584505763 13432697738633873376758645)
                  ·
                    refine ⟨1259315412996925629071123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13432697738633873376758645 1259315412996925629071123)
                    ·
                      rfl

theorem cell23_7357524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_7357524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357524 prefixEnd_7357524 := by exact prefixLift 7357524
  have htrace : WordTrace (prefixWord ++ tailWord_7357524) baseStart_7357524 baseEnd_7357524 := by
    simpa [prefixWord, tailWord_7357524, baseEnd_7357524] using wordTrace_append hprefix tailTrace_7357524
  have hstable : (prefixWord ++ tailWord_7357524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357524).length < 2 ^ (prefixWord ++ tailWord_7357524).sum := by decide
  have hdescent : baseEnd_7357524 < baseStart_7357524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357527 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 4]
def baseStart_7357527 : Nat := 118140960795 + 7357527 * 2 ^ 59
def prefixEnd_7357527 : Nat := 4983230072969 + 3 ^ 40 * 7357527 * 2
def baseEnd_7357527 : Nat := 3777947779432740375475855

theorem tailTrace_7357527 : CollatzResearch.WordTrace tailWord_7357527 prefixEnd_7357527 3777947779432740375475855 := by
  unfold tailWord_7357527
  simp only [CollatzResearch.WordTrace]
  refine ⟨268351055615943719416414835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178900703743962479610943223 268351055615943719416414835)
  ·
    refine ⟨402526583423915579124622253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268351055615943719416414835 402526583423915579124622253)
    ·
      refine ⟨150947468783968342171733345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402526583423915579124622253 150947468783968342171733345)
      ·
        refine ⟨113210601587976256628800009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150947468783968342171733345 113210601587976256628800009)
        ·
          refine ⟨84907951190982192471600007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113210601587976256628800009 84907951190982192471600007)
          ·
            refine ⟨127361926786473288707400011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84907951190982192471600007 127361926786473288707400011)
            ·
              refine ⟨191042890179709933061100017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127361926786473288707400011 191042890179709933061100017)
              ·
                refine ⟨143282167634782449795825013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191042890179709933061100017 143282167634782449795825013)
                ·
                  refine ⟨13432703215760854668358595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143282167634782449795825013 13432703215760854668358595)
                  ·
                    refine ⟨20149054823641282002537893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13432703215760854668358595 20149054823641282002537893)
                    ·
                      refine ⟨3777947779432740375475855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20149054823641282002537893 3777947779432740375475855)
                      ·
                        rfl

theorem cell23_7357527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_7357527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357527 prefixEnd_7357527 := by exact prefixLift 7357527
  have htrace : WordTrace (prefixWord ++ tailWord_7357527) baseStart_7357527 baseEnd_7357527 := by
    simpa [prefixWord, tailWord_7357527, baseEnd_7357527] using wordTrace_append hprefix tailTrace_7357527
  have hstable : (prefixWord ++ tailWord_7357527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357527).length < 2 ^ (prefixWord ++ tailWord_7357527).sum := by decide
  have hdescent : baseEnd_7357527 < baseStart_7357527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357538 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_7357538 : Nat := 118140960795 + 7357538 * 2 ^ 59
def prefixEnd_7357538 : Nat := 4983230072969 + 3 ^ 40 * 7357538 * 2
def baseEnd_7357538 : Nat := 3777953427719939832438305

theorem tailTrace_7357538 : CollatzResearch.WordTrace tailWord_7357538 prefixEnd_7357538 3777953427719939832438305 := by
  unfold tailWord_7357538
  simp only [CollatzResearch.WordTrace]
  refine ⟨67087864204725967073766317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178900971212602578863376845 67087864204725967073766317)
  ·
    refine ⟨25157949076772237652662369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67087864204725967073766317 25157949076772237652662369)
    ·
      refine ⟨18868461807579178239496777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25157949076772237652662369 18868461807579178239496777)
      ·
        refine ⟨14151346355684383679622583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18868461807579178239496777 14151346355684383679622583)
        ·
          refine ⟨21227019533526575519433875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14151346355684383679622583 21227019533526575519433875)
          ·
            refine ⟨31840529300289863279150813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21227019533526575519433875 31840529300289863279150813)
            ·
              refine ⟨11940198487608698729681555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31840529300289863279150813 11940198487608698729681555)
              ·
                refine ⟨17910297731413048094522333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11940198487608698729681555 17910297731413048094522333)
                ·
                  refine ⟨6716361649279893035445875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17910297731413048094522333 6716361649279893035445875)
                  ·
                    refine ⟨10074542473919839553168813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6716361649279893035445875 10074542473919839553168813)
                    ·
                      refine ⟨3777953427719939832438305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10074542473919839553168813 3777953427719939832438305)
                      ·
                        rfl

theorem cell23_7357538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_7357538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357538 prefixEnd_7357538 := by exact prefixLift 7357538
  have htrace : WordTrace (prefixWord ++ tailWord_7357538) baseStart_7357538 baseEnd_7357538 := by
    simpa [prefixWord, tailWord_7357538, baseEnd_7357538] using wordTrace_append hprefix tailTrace_7357538
  have hstable : (prefixWord ++ tailWord_7357538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357538).length < 2 ^ (prefixWord ++ tailWord_7357538).sum := by decide
  have hdescent : baseEnd_7357538 < baseStart_7357538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
