import V185TrunkScan23Chunk1241

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7357564 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_7357564 : Nat := 118140960795 + 7357564 * 2 ^ 59
def prefixEnd_7357564 : Nat := 4983230072969 + 3 ^ 40 * 7357564 * 2
def baseEnd_7357564 : Nat := 3777966778216956730713185

theorem tailTrace_7357564 : CollatzResearch.WordTrace tailWord_7357564 prefixEnd_7357564 3777966778216956730713185 := by
  unfold tailWord_7357564
  simp only [CollatzResearch.WordTrace]
  refine ⟨134176202558404837367755873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178901603411206449823674497 134176202558404837367755873)
  ·
    refine ⟨100632151918803628025816905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134176202558404837367755873 100632151918803628025816905)
    ·
      refine ⟨75474113939102721019362679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100632151918803628025816905 75474113939102721019362679)
      ·
        refine ⟨113211170908654081529044019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75474113939102721019362679 113211170908654081529044019)
        ·
          refine ⟨169816756362981122293566029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113211170908654081529044019 169816756362981122293566029)
          ·
            refine ⟨63681283636117920860087261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169816756362981122293566029 63681283636117920860087261)
            ·
              refine ⟨23880481363544220322532723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63681283636117920860087261 23880481363544220322532723)
              ·
                refine ⟨35820722045316330483799085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23880481363544220322532723 35820722045316330483799085)
                ·
                  refine ⟨13432770766993623931424657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35820722045316330483799085 13432770766993623931424657)
                  ·
                    refine ⟨10074578075245217948568493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13432770766993623931424657 10074578075245217948568493)
                    ·
                      refine ⟨3777966778216956730713185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10074578075245217948568493 3777966778216956730713185)
                      ·
                        rfl

theorem cell23_7357564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_7357564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357564 prefixEnd_7357564 := by exact prefixLift 7357564
  have htrace : WordTrace (prefixWord ++ tailWord_7357564) baseStart_7357564 baseEnd_7357564 := by
    simpa [prefixWord, tailWord_7357564, baseEnd_7357564] using wordTrace_append hprefix tailTrace_7357564
  have hstable : (prefixWord ++ tailWord_7357564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357564).length < 2 ^ (prefixWord ++ tailWord_7357564).sum := by decide
  have hdescent : baseEnd_7357564 < baseStart_7357564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357597 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_7357597 : Nat := 118140960795 + 7357597 * 2 ^ 59
def prefixEnd_7357597 : Nat := 4983230072969 + 3 ^ 40 * 7357597 * 2
def baseEnd_7357597 : Nat := 1259327907692851700533511

theorem tailTrace_7357597 : CollatzResearch.WordTrace tailWord_7357597 prefixEnd_7357597 1259327907692851700533511 := by
  unfold tailWord_7357597
  simp only [CollatzResearch.WordTrace]
  refine ⟨268353608725690121371463045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178902405817126747580975363 268353608725690121371463045)
  ·
    refine ⟨50316301636066897757149321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268353608725690121371463045 50316301636066897757149321)
    ·
      refine ⟨37737226227050173317861991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50316301636066897757149321 37737226227050173317861991)
      ·
        refine ⟨56605839340575259976792987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37737226227050173317861991 56605839340575259976792987)
        ·
          refine ⟨84908759010862889965189481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56605839340575259976792987 84908759010862889965189481)
          ·
            refine ⟨63681569258147167473892111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84908759010862889965189481 63681569258147167473892111)
            ·
              refine ⟨95522353887220751210838167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63681569258147167473892111 95522353887220751210838167)
              ·
                refine ⟨143283530830831126816257251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95522353887220751210838167 143283530830831126816257251)
                ·
                  refine ⟨214925296246246690224385877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143283530830831126816257251 214925296246246690224385877)
                  ·
                    refine ⟨1259327907692851700533511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 214925296246246690224385877 1259327907692851700533511)
                    ·
                      rfl

theorem cell23_7357597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_7357597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357597 prefixEnd_7357597 := by exact prefixLift 7357597
  have htrace : WordTrace (prefixWord ++ tailWord_7357597) baseStart_7357597 baseEnd_7357597 := by
    simpa [prefixWord, tailWord_7357597, baseEnd_7357597] using wordTrace_append hprefix tailTrace_7357597
  have hstable : (prefixWord ++ tailWord_7357597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357597).length < 2 ^ (prefixWord ++ tailWord_7357597).sum := by decide
  have hdescent : baseEnd_7357597 < baseStart_7357597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357637 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_7357637 : Nat := 118140960795 + 7357637 * 2 ^ 59
def prefixEnd_7357637 : Nat := 4983230072969 + 3 ^ 40 * 7357637 * 2
def baseEnd_7357637 : Nat := 3778004262304734945100349

theorem tailTrace_7357637 : CollatzResearch.WordTrace tailWord_7357637 prefixEnd_7357637 3778004262304734945100349 := by
  unfold tailWord_7357637
  simp only [CollatzResearch.WordTrace]
  refine ⟨268355067645545208202919165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178903378430363472135279443 268355067645545208202919165)
  ·
    refine ⟨100633150367079453076094687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268355067645545208202919165 100633150367079453076094687)
    ·
      refine ⟨150949725550619179614142031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100633150367079453076094687 150949725550619179614142031)
      ·
        refine ⟨226424588325928769421213047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150949725550619179614142031 226424588325928769421213047)
        ·
          refine ⟨339636882488893154131819571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226424588325928769421213047 339636882488893154131819571)
          ·
            refine ⟨509455323733339731197729357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339636882488893154131819571 509455323733339731197729357)
            ·
              refine ⟨191045746400002399199148509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 509455323733339731197729357 191045746400002399199148509)
              ·
                refine ⟨71642154900000899699680691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191045746400002399199148509 71642154900000899699680691)
                ·
                  refine ⟨107463232350001349549521037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71642154900000899699680691 107463232350001349549521037)
                  ·
                    refine ⟨40298712131250506081070389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107463232350001349549521037 40298712131250506081070389)
                    ·
                      refine ⟨3778004262304734945100349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40298712131250506081070389 3778004262304734945100349)
                      ·
                        rfl

theorem cell23_7357637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_7357637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357637 prefixEnd_7357637 := by exact prefixLift 7357637
  have htrace : WordTrace (prefixWord ++ tailWord_7357637) baseStart_7357637 baseEnd_7357637 := by
    simpa [prefixWord, tailWord_7357637, baseEnd_7357637] using wordTrace_append hprefix tailTrace_7357637
  have hstable : (prefixWord ++ tailWord_7357637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357637).length < 2 ^ (prefixWord ++ tailWord_7357637).sum := by decide
  have hdescent : baseEnd_7357637 < baseStart_7357637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357651 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 4, 2, 2]
def baseStart_7357651 : Nat := 118140960795 + 7357651 * 2 ^ 59
def prefixEnd_7357651 : Nat := 4983230072969 + 3 ^ 40 * 7357651 * 2
def baseEnd_7357651 : Nat := 3778011451033897890325285

theorem tailTrace_7357651 : CollatzResearch.WordTrace tailWord_7357651 prefixEnd_7357651 3778011451033897890325285 := by
  unfold tailWord_7357651
  simp only [CollatzResearch.WordTrace]
  refine ⟨268355578267494488593928807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178903718844996325729285871 268355578267494488593928807)
  ·
    refine ⟨402533367401241732890893211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268355578267494488593928807 402533367401241732890893211)
    ·
      refine ⟨603800051101862599336339817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402533367401241732890893211 603800051101862599336339817)
      ·
        refine ⟨452850038326396949502254863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 603800051101862599336339817 452850038326396949502254863)
        ·
          refine ⟨679275057489595424253382295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452850038326396949502254863 679275057489595424253382295)
          ·
            refine ⟨1018912586234393136380073443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679275057489595424253382295 1018912586234393136380073443)
            ·
              refine ⟨1528368879351589704570110165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018912586234393136380073443 1528368879351589704570110165)
              ·
                refine ⟨35821145609802883700861957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1528368879351589704570110165 35821145609802883700861957)
                ·
                  refine ⟨6716464801838040693911617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35821145609802883700861957 6716464801838040693911617)
                  ·
                    refine ⟨5037348601378530520433713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6716464801838040693911617 5037348601378530520433713)
                    ·
                      refine ⟨3778011451033897890325285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5037348601378530520433713 3778011451033897890325285)
                      ·
                        rfl

theorem cell23_7357651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 2, 2].length) (baseStart_7357651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357651 prefixEnd_7357651 := by exact prefixLift 7357651
  have htrace : WordTrace (prefixWord ++ tailWord_7357651) baseStart_7357651 baseEnd_7357651 := by
    simpa [prefixWord, tailWord_7357651, baseEnd_7357651] using wordTrace_append hprefix tailTrace_7357651
  have hstable : (prefixWord ++ tailWord_7357651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357651).length < 2 ^ (prefixWord ++ tailWord_7357651).sum := by decide
  have hdescent : baseEnd_7357651 < baseStart_7357651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357664 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 4]
def baseStart_7357664 : Nat := 118140960795 + 7357664 * 2 ^ 59
def prefixEnd_7357664 : Nat := 4983230072969 + 3 ^ 40 * 7357664 * 2
def baseEnd_7357664 : Nat := 3778018126282406339462725

theorem tailTrace_7357664 : CollatzResearch.WordTrace tailWord_7357664 prefixEnd_7357664 3778018126282406339462725 := by
  unfold tailWord_7357664
  simp only [CollatzResearch.WordTrace]
  refine ⟨134178026208223695907076023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178904034944298261209434697 134178026208223695907076023)
  ·
    refine ⟨201267039312335543860614035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134178026208223695907076023 201267039312335543860614035)
    ·
      refine ⟨301900558968503315790921053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201267039312335543860614035 301900558968503315790921053)
      ·
        refine ⟨113212709613188743421595395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301900558968503315790921053 113212709613188743421595395)
        ·
          refine ⟨169819064419783115132393093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113212709613188743421595395 169819064419783115132393093)
          ·
            refine ⟨31841074578709334087323705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169819064419783115132393093 31841074578709334087323705)
            ·
              refine ⟨23880805934032000565492779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31841074578709334087323705 23880805934032000565492779)
              ·
                refine ⟨35821208901048000848239169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23880805934032000565492779 35821208901048000848239169)
                ·
                  refine ⟨26865906675786000636179377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35821208901048000848239169 26865906675786000636179377)
                  ·
                    refine ⟨20149430006839500477134533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26865906675786000636179377 20149430006839500477134533)
                    ·
                      refine ⟨3778018126282406339462725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20149430006839500477134533 3778018126282406339462725)
                      ·
                        rfl

theorem cell23_7357664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_7357664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357664 prefixEnd_7357664 := by exact prefixLift 7357664
  have htrace : WordTrace (prefixWord ++ tailWord_7357664) baseStart_7357664 baseEnd_7357664 := by
    simpa [prefixWord, tailWord_7357664, baseEnd_7357664] using wordTrace_append hprefix tailTrace_7357664
  have hstable : (prefixWord ++ tailWord_7357664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357664).length < 2 ^ (prefixWord ++ tailWord_7357664).sum := by decide
  have hdescent : baseEnd_7357664 < baseStart_7357664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357668 : List Nat := [2, 3, 1, 1, 1, 2, 2, 5, 2, 2, 2]
def baseStart_7357668 : Nat := 118140960795 + 7357668 * 2 ^ 59
def prefixEnd_7357668 : Nat := 4983230072969 + 3 ^ 40 * 7357668 * 2
def baseEnd_7357668 : Nat := 3778020180205024323812707

theorem tailTrace_7357668 : CollatzResearch.WordTrace tailWord_7357668 prefixEnd_7357668 3778020180205024323812707 := by
  unfold tailWord_7357668
  simp only [CollatzResearch.WordTrace]
  refine ⟨134178099154216450248648829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178904132205621933664865105 134178099154216450248648829)
  ·
    refine ⟨50316787182831168843243311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134178099154216450248648829 50316787182831168843243311)
    ·
      refine ⟨75475180774246753264864967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50316787182831168843243311 75475180774246753264864967)
      ·
        refine ⟨113212771161370129897297451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75475180774246753264864967 113212771161370129897297451)
        ·
          refine ⟨169819156742055194845946177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113212771161370129897297451 169819156742055194845946177)
          ·
            refine ⟨127364367556541396134459633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169819156742055194845946177 127364367556541396134459633)
            ·
              refine ⟨95523275667406047100844725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127364367556541396134459633 95523275667406047100844725)
              ·
                refine ⟨8955307093819316915704193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95523275667406047100844725 8955307093819316915704193)
                ·
                  refine ⟨6716480320364487686778145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8955307093819316915704193 6716480320364487686778145)
                  ·
                    refine ⟨5037360240273365765083609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6716480320364487686778145 5037360240273365765083609)
                    ·
                      refine ⟨3778020180205024323812707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5037360240273365765083609 3778020180205024323812707)
                      ·
                        rfl

theorem cell23_7357668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_7357668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357668 prefixEnd_7357668 := by exact prefixLift 7357668
  have htrace : WordTrace (prefixWord ++ tailWord_7357668) baseStart_7357668 baseEnd_7357668 := by
    simpa [prefixWord, tailWord_7357668, baseEnd_7357668] using wordTrace_append hprefix tailTrace_7357668
  have hstable : (prefixWord ++ tailWord_7357668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357668).length < 2 ^ (prefixWord ++ tailWord_7357668).sum := by decide
  have hdescent : baseEnd_7357668 < baseStart_7357668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357674 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 7]
def baseStart_7357674 : Nat := 118140960795 + 7357674 * 2 ^ 59
def prefixEnd_7357674 : Nat := 4983230072969 + 3 ^ 40 * 7357674 * 2
def baseEnd_7357674 : Nat := 419780362343216811148631

theorem tailTrace_7357674 : CollatzResearch.WordTrace tailWord_7357674 prefixEnd_7357674 419780362343216811148631 := by
  unfold tailWord_7357674
  simp only [CollatzResearch.WordTrace]
  refine ⟨67089104286602790880504019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178904278097607442348010717 67089104286602790880504019)
  ·
    refine ⟨100633656429904186320756029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67089104286602790880504019 100633656429904186320756029)
    ·
      refine ⟨37737621161214069870283511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100633656429904186320756029 37737621161214069870283511)
      ·
        refine ⟨56606431741821104805425267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37737621161214069870283511 56606431741821104805425267)
        ·
          refine ⟨84909647612731657208137901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56606431741821104805425267 84909647612731657208137901)
          ·
            refine ⟨31841117854774371453051713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84909647612731657208137901 31841117854774371453051713)
            ·
              refine ⟨23880838391080778589788785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31841117854774371453051713 23880838391080778589788785)
              ·
                refine ⟨17910628793310583942341589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23880838391080778589788785 17910628793310583942341589)
                ·
                  refine ⟨419780362343216811148631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17910628793310583942341589 419780362343216811148631)
                  ·
                    rfl

theorem cell23_7357674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_7357674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357674 prefixEnd_7357674 := by exact prefixLift 7357674
  have htrace : WordTrace (prefixWord ++ tailWord_7357674) baseStart_7357674 baseEnd_7357674 := by
    simpa [prefixWord, tailWord_7357674, baseEnd_7357674] using wordTrace_append hprefix tailTrace_7357674
  have hstable : (prefixWord ++ tailWord_7357674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357674).length < 2 ^ (prefixWord ++ tailWord_7357674).sum := by decide
  have hdescent : baseEnd_7357674 < baseStart_7357674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357708 : List Nat := [2, 2, 1, 2, 2, 4, 3, 2, 5]
def baseStart_7357708 : Nat := 118140960795 + 7357708 * 2 ^ 59
def prefixEnd_7357708 : Nat := 4983230072969 + 3 ^ 40 * 7357708 * 2
def baseEnd_7357708 : Nat := 419782302159022685256947

theorem tailTrace_7357708 : CollatzResearch.WordTrace tailWord_7357708 prefixEnd_7357708 419782302159022685256947 := by
  unfold tailWord_7357708
  simp only [CollatzResearch.WordTrace]
  refine ⟨134178828614143993664376889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178905104818858658219169185 134178828614143993664376889)
  ·
    refine ⟨100634121460607995248282667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134178828614143993664376889 100634121460607995248282667)
    ·
      refine ⟨150951182190911992872424001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100634121460607995248282667 150951182190911992872424001)
      ·
        refine ⟨113213386643183994654318001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150951182190911992872424001 113213386643183994654318001)
        ·
          refine ⟨84910039982387995990738501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113213386643183994654318001 84910039982387995990738501)
          ·
            refine ⟨15920632496697749248263469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84910039982387995990738501 15920632496697749248263469)
            ·
              refine ⟨5970237186261655968098801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15920632496697749248263469 5970237186261655968098801)
              ·
                refine ⟨4477677889696241976074101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5970237186261655968098801 4477677889696241976074101)
                ·
                  refine ⟨419782302159022685256947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4477677889696241976074101 419782302159022685256947)
                  ·
                    rfl

theorem cell23_7357708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 5].length) (baseStart_7357708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357708 prefixEnd_7357708 := by exact prefixLift 7357708
  have htrace : WordTrace (prefixWord ++ tailWord_7357708) baseStart_7357708 baseEnd_7357708 := by
    simpa [prefixWord, tailWord_7357708, baseEnd_7357708] using wordTrace_append hprefix tailTrace_7357708
  have hstable : (prefixWord ++ tailWord_7357708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357708).length < 2 ^ (prefixWord ++ tailWord_7357708).sum := by decide
  have hdescent : baseEnd_7357708 < baseStart_7357708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357724 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_7357724 : Nat := 118140960795 + 7357724 * 2 ^ 59
def prefixEnd_7357724 : Nat := 4983230072969 + 3 ^ 40 * 7357724 * 2
def baseEnd_7357724 : Nat := 3778048935121676104712449

theorem tailTrace_7357724 : CollatzResearch.WordTrace tailWord_7357724 prefixEnd_7357724 3778048935121676104712449 := by
  unfold tailWord_7357724
  simp only [CollatzResearch.WordTrace]
  refine ⟨134179120398115011030668113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178905493864153348040890817 134179120398115011030668113)
  ·
    refine ⟨100634340298586258273001085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134179120398115011030668113 100634340298586258273001085)
    ·
      refine ⟨37737877611969846852375407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100634340298586258273001085 37737877611969846852375407)
      ·
        refine ⟨56606816417954770278563111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37737877611969846852375407 56606816417954770278563111)
        ·
          refine ⟨84910224626932155417844667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56606816417954770278563111 84910224626932155417844667)
          ·
            refine ⟨127365336940398233126767001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84910224626932155417844667 127365336940398233126767001)
            ·
              refine ⟨95524002705298674845075251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127365336940398233126767001 95524002705298674845075251)
              ·
                refine ⟨143286004057948012267612877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95524002705298674845075251 143286004057948012267612877)
                ·
                  refine ⟨53732251521730504600354829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143286004057948012267612877 53732251521730504600354829)
                  ·
                    refine ⟨20149594320648939225133061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53732251521730504600354829 20149594320648939225133061)
                    ·
                      refine ⟨3778048935121676104712449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20149594320648939225133061 3778048935121676104712449)
                      ·
                        rfl

theorem cell23_7357724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_7357724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357724 prefixEnd_7357724 := by exact prefixLift 7357724
  have htrace : WordTrace (prefixWord ++ tailWord_7357724) baseStart_7357724 baseEnd_7357724 := by
    simpa [prefixWord, tailWord_7357724, baseEnd_7357724] using wordTrace_append hprefix tailTrace_7357724
  have hstable : (prefixWord ++ tailWord_7357724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357724).length < 2 ^ (prefixWord ++ tailWord_7357724).sum := by decide
  have hdescent : baseEnd_7357724 < baseStart_7357724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357738 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 2, 5]
def baseStart_7357738 : Nat := 118140960795 + 7357738 * 2 ^ 59
def prefixEnd_7357738 : Nat := 4983230072969 + 3 ^ 40 * 7357738 * 2
def baseEnd_7357738 : Nat := 1259352041283613016645795

theorem tailTrace_7357738 : CollatzResearch.WordTrace tailWord_7357738 prefixEnd_7357738 1259352041283613016645795 := by
  unfold tailWord_7357738
  simp only [CollatzResearch.WordTrace]
  refine ⟨67089687854544825613086467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178905834278786201634897245 67089687854544825613086467)
  ·
    refine ⟨100634531781817238419629701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67089687854544825613086467 100634531781817238419629701)
    ·
      refine ⟨18868974709090732203680569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100634531781817238419629701 18868974709090732203680569)
      ·
        refine ⟨14151731031818049152760427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18868974709090732203680569 14151731031818049152760427)
        ·
          refine ⟨21227596547727073729140641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14151731031818049152760427 21227596547727073729140641)
          ·
            refine ⟨15920697410795305296855481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21227596547727073729140641 15920697410795305296855481)
            ·
              refine ⟨11940523058096478972641611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15920697410795305296855481 11940523058096478972641611)
              ·
                refine ⟨17910784587144718458962417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11940523058096478972641611 17910784587144718458962417)
                ·
                  refine ⟨13433088440358538844221813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17910784587144718458962417 13433088440358538844221813)
                  ·
                    refine ⟨1259352041283613016645795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13433088440358538844221813 1259352041283613016645795)
                    ·
                      rfl

theorem cell23_7357738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_7357738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357738 prefixEnd_7357738 := by exact prefixLift 7357738
  have htrace : WordTrace (prefixWord ++ tailWord_7357738) baseStart_7357738 baseEnd_7357738 := by
    simpa [prefixWord, tailWord_7357738, baseEnd_7357738] using wordTrace_append hprefix tailTrace_7357738
  have hstable : (prefixWord ++ tailWord_7357738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357738).length < 2 ^ (prefixWord ++ tailWord_7357738).sum := by decide
  have hdescent : baseEnd_7357738 < baseStart_7357738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357754 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_7357754 : Nat := 118140960795 + 7357754 * 2 ^ 59
def prefixEnd_7357754 : Nat := 4983230072969 + 3 ^ 40 * 7357754 * 2
def baseEnd_7357754 : Nat := 3778064339541310987337311

theorem tailTrace_7357754 : CollatzResearch.WordTrace tailWord_7357754 prefixEnd_7357754 3778064339541310987337311 := by
  unfold tailWord_7357754
  simp only [CollatzResearch.WordTrace]
  refine ⟨67089833746530334296232079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178906223324080891456618877 67089833746530334296232079)
  ·
    refine ⟨100634750619795501444348119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67089833746530334296232079 100634750619795501444348119)
    ·
      refine ⟨150952125929693252166522179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100634750619795501444348119 150952125929693252166522179)
      ·
        refine ⟨226428188894539878249783269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150952125929693252166522179 226428188894539878249783269)
        ·
          refine ⟨42455285417726227171834363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226428188894539878249783269 42455285417726227171834363)
          ·
            refine ⟨63682928126589340757751545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42455285417726227171834363 63682928126589340757751545)
            ·
              refine ⟨47762196094942005568313659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63682928126589340757751545 47762196094942005568313659)
              ·
                refine ⟨71643294142413008352470489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47762196094942005568313659 71643294142413008352470489)
                ·
                  refine ⟨53732470606809756264352867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71643294142413008352470489 53732470606809756264352867)
                  ·
                    refine ⟨80598705910214634396529301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53732470606809756264352867 80598705910214634396529301)
                    ·
                      refine ⟨3778064339541310987337311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80598705910214634396529301 3778064339541310987337311)
                      ·
                        rfl

theorem cell23_7357754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_7357754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357754 prefixEnd_7357754 := by exact prefixLift 7357754
  have htrace : WordTrace (prefixWord ++ tailWord_7357754) baseStart_7357754 baseEnd_7357754 := by
    simpa [prefixWord, tailWord_7357754, baseEnd_7357754] using wordTrace_append hprefix tailTrace_7357754
  have hstable : (prefixWord ++ tailWord_7357754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357754).length < 2 ^ (prefixWord ++ tailWord_7357754).sum := by decide
  have hdescent : baseEnd_7357754 < baseStart_7357754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357758 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_7357758 : Nat := 118140960795 + 7357758 * 2 ^ 59
def prefixEnd_7357758 : Nat := 4983230072969 + 3 ^ 40 * 7357758 * 2
def baseEnd_7357758 : Nat := 3778066393463928971687293

theorem tailTrace_7357758 : CollatzResearch.WordTrace tailWord_7357758 prefixEnd_7357758 3778066393463928971687293 := by
  unfold tailWord_7357758
  simp only [CollatzResearch.WordTrace]
  refine ⟨33544935109763355733509241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178906320585404563912049285 33544935109763355733509241)
  ·
    refine ⟨25158701332322516800131931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33544935109763355733509241 25158701332322516800131931)
    ·
      refine ⟨37738051998483775200197897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25158701332322516800131931 37738051998483775200197897)
      ·
        refine ⟨28303538998862831400148423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37738051998483775200197897 28303538998862831400148423)
        ·
          refine ⟨42455308498294247100222635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28303538998862831400148423 42455308498294247100222635)
          ·
            refine ⟨63682962747441370650333953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42455308498294247100222635 63682962747441370650333953)
            ·
              refine ⟨47762222060581027987750465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63682962747441370650333953 47762222060581027987750465)
              ·
                refine ⟨35821666545435770990812849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47762222060581027987750465 35821666545435770990812849)
                ·
                  refine ⟨26866249909076828243109637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35821666545435770990812849 26866249909076828243109637)
                  ·
                    refine ⟨5037421857951905295583057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26866249909076828243109637 5037421857951905295583057)
                    ·
                      refine ⟨3778066393463928971687293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5037421857951905295583057 3778066393463928971687293)
                      ·
                        rfl

theorem cell23_7357758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_7357758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357758 prefixEnd_7357758 := by exact prefixLift 7357758
  have htrace : WordTrace (prefixWord ++ tailWord_7357758) baseStart_7357758 baseEnd_7357758 := by
    simpa [prefixWord, tailWord_7357758, baseEnd_7357758] using wordTrace_append hprefix tailTrace_7357758
  have hstable : (prefixWord ++ tailWord_7357758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357758).length < 2 ^ (prefixWord ++ tailWord_7357758).sum := by decide
  have hdescent : baseEnd_7357758 < baseStart_7357758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357781 : List Nat := [1, 3, 2, 2, 3, 1, 2, 3, 6]
def baseStart_7357781 : Nat := 118140960795 + 7357781 * 2 ^ 59
def prefixEnd_7357781 : Nat := 4983230072969 + 3 ^ 40 * 7357781 * 2
def baseEnd_7357781 : Nat := 419786467057664709077743

theorem tailTrace_7357781 : CollatzResearch.WordTrace tailWord_7357781 prefixEnd_7357781 419786467057664709077743 := by
  unfold tailWord_7357781
  simp only [CollatzResearch.WordTrace]
  refine ⟨268360319757023520796161197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178906879838015680530774131 268360319757023520796161197)
  ·
    refine ⟨100635119908883820298560449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268360319757023520796161197 100635119908883820298560449)
    ·
      refine ⟨75476339931662865223920337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100635119908883820298560449 75476339931662865223920337)
      ·
        refine ⟨56607254948747148917940253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75476339931662865223920337 56607254948747148917940253)
        ·
          refine ⟨21227720605780180844227595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56607254948747148917940253 21227720605780180844227595)
          ·
            refine ⟨31841580908670271266341393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21227720605780180844227595 31841580908670271266341393)
            ·
              refine ⟨23881185681502703449756045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31841580908670271266341393 23881185681502703449756045)
              ·
                refine ⟨8955444630563513793658517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23881185681502703449756045 8955444630563513793658517)
                ·
                  refine ⟨419786467057664709077743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8955444630563513793658517 419786467057664709077743)
                  ·
                    rfl

theorem cell23_7357781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 6].length) (baseStart_7357781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357781 prefixEnd_7357781 := by exact prefixLift 7357781
  have htrace : WordTrace (prefixWord ++ tailWord_7357781) baseStart_7357781 baseEnd_7357781 := by
    simpa [prefixWord, tailWord_7357781, baseEnd_7357781] using wordTrace_append hprefix tailTrace_7357781
  have hstable : (prefixWord ++ tailWord_7357781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357781).length < 2 ^ (prefixWord ++ tailWord_7357781).sum := by decide
  have hdescent : baseEnd_7357781 < baseStart_7357781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357789 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 2, 5]
def baseStart_7357789 : Nat := 118140960795 + 7357789 * 2 ^ 59
def prefixEnd_7357789 : Nat := 4983230072969 + 3 ^ 40 * 7357789 * 2
def baseEnd_7357789 : Nat := 1259360770454739450133217

theorem tailTrace_7357789 : CollatzResearch.WordTrace tailWord_7357789 prefixEnd_7357789 1259360770454739450133217 := by
  unfold tailWord_7357789
  simp only [CollatzResearch.WordTrace]
  refine ⟨268360611540994538162452421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178907074360663025441634947 268360611540994538162452421)
  ·
    refine ⟨50317614663936475905459829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268360611540994538162452421 50317614663936475905459829)
    ·
      refine ⟨4717276374744044616136859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50317614663936475905459829 4717276374744044616136859)
      ·
        refine ⟨7075914562116066924205289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4717276374744044616136859 7075914562116066924205289)
        ·
          refine ⟨5306935921587050193153967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7075914562116066924205289 5306935921587050193153967)
          ·
            refine ⟨7960403882380575289730951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306935921587050193153967 7960403882380575289730951)
            ·
              refine ⟨11940605823570862934596427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7960403882380575289730951 11940605823570862934596427)
              ·
                refine ⟨17910908735356294401894641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11940605823570862934596427 17910908735356294401894641)
                ·
                  refine ⟨13433181551517220801420981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17910908735356294401894641 13433181551517220801420981)
                  ·
                    refine ⟨1259360770454739450133217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13433181551517220801420981 1259360770454739450133217)
                    ·
                      rfl

theorem cell23_7357789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_7357789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357789 prefixEnd_7357789 := by exact prefixLift 7357789
  have htrace : WordTrace (prefixWord ++ tailWord_7357789) baseStart_7357789 baseEnd_7357789 := by
    simpa [prefixWord, tailWord_7357789, baseEnd_7357789] using wordTrace_append hprefix tailTrace_7357789
  have hstable : (prefixWord ++ tailWord_7357789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357789).length < 2 ^ (prefixWord ++ tailWord_7357789).sum := by decide
  have hdescent : baseEnd_7357789 < baseStart_7357789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357802 : List Nat := [3, 1, 3, 3, 2, 1, 2, 3, 1, 4]
def baseStart_7357802 : Nat := 118140960795 + 7357802 * 2 ^ 59
def prefixEnd_7357802 : Nat := 4983230072969 + 3 ^ 40 * 7357802 * 2
def baseEnd_7357802 : Nat := 1259362995537575599845697

theorem tailTrace_7357802 : CollatzResearch.WordTrace tailWord_7357802 prefixEnd_7357802 1259362995537575599845697 := by
  unfold tailWord_7357802
  simp only [CollatzResearch.WordTrace]
  refine ⟨67090271422486860345668915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178907390459964960921783773 67090271422486860345668915)
  ·
    refine ⟨100635407133730290518503373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67090271422486860345668915 100635407133730290518503373)
    ·
      refine ⟨37738277675148858944438765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100635407133730290518503373 37738277675148858944438765)
      ·
        refine ⟨14151854128180822104164537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37738277675148858944438765 14151854128180822104164537)
        ·
          refine ⟨10613890596135616578123403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14151854128180822104164537 10613890596135616578123403)
          ·
            refine ⟨15920835894203424867185105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10613890596135616578123403 15920835894203424867185105)
            ·
              refine ⟨11940626920652568650388829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15920835894203424867185105 11940626920652568650388829)
              ·
                refine ⟨4477735095244713243895811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11940626920652568650388829 4477735095244713243895811)
                ·
                  refine ⟨6716602642867069865843717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4477735095244713243895811 6716602642867069865843717)
                  ·
                    refine ⟨1259362995537575599845697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6716602642867069865843717 1259362995537575599845697)
                    ·
                      rfl

theorem cell23_7357802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_7357802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357802 prefixEnd_7357802 := by exact prefixLift 7357802
  have htrace : WordTrace (prefixWord ++ tailWord_7357802) baseStart_7357802 baseEnd_7357802 := by
    simpa [prefixWord, tailWord_7357802, baseEnd_7357802] using wordTrace_append hprefix tailTrace_7357802
  have hstable : (prefixWord ++ tailWord_7357802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357802).length < 2 ^ (prefixWord ++ tailWord_7357802).sum := by decide
  have hdescent : baseEnd_7357802 < baseStart_7357802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357824 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 3, 6]
def baseStart_7357824 : Nat := 118140960795 + 7357824 * 2 ^ 59
def prefixEnd_7357824 : Nat := 4983230072969 + 3 ^ 40 * 7357824 * 2
def baseEnd_7357824 : Nat := 1259366761062375237820663

theorem tailTrace_7357824 : CollatzResearch.WordTrace tailWord_7357824 prefixEnd_7357824 1259366761062375237820663 := by
  unfold tailWord_7357824
  simp only [CollatzResearch.WordTrace]
  refine ⟨134180944047933869569988263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178907925397245159426651017 134180944047933869569988263)
  ·
    refine ⟨201271416071900804354982395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134180944047933869569988263 201271416071900804354982395)
    ·
      refine ⟨301907124107851206532473593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201271416071900804354982395 301907124107851206532473593)
      ·
        refine ⟨226430343080888404899355195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301907124107851206532473593 226430343080888404899355195)
        ·
          refine ⟨339645514621332607349032793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226430343080888404899355195 339645514621332607349032793)
          ·
            refine ⟨254734135965999455511774595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339645514621332607349032793 254734135965999455511774595)
            ·
              refine ⟨382101203948999183267661893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254734135965999455511774595 382101203948999183267661893)
              ·
                refine ⟨71643975740437346862686605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 382101203948999183267661893 71643975740437346862686605)
                ·
                  refine ⟨26866490902664005073507477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71643975740437346862686605 26866490902664005073507477)
                  ·
                    refine ⟨1259366761062375237820663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26866490902664005073507477 1259366761062375237820663)
                    ·
                      rfl

theorem cell23_7357824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3, 6].length) (baseStart_7357824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357824 prefixEnd_7357824 := by exact prefixLift 7357824
  have htrace : WordTrace (prefixWord ++ tailWord_7357824) baseStart_7357824 baseEnd_7357824 := by
    simpa [prefixWord, tailWord_7357824, baseEnd_7357824] using wordTrace_append hprefix tailTrace_7357824
  have hstable : (prefixWord ++ tailWord_7357824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357824).length < 2 ^ (prefixWord ++ tailWord_7357824).sum := by decide
  have hdescent : baseEnd_7357824 < baseStart_7357824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357858 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_7357858 : Nat := 118140960795 + 7357858 * 2 ^ 59
def prefixEnd_7357858 : Nat := 4983230072969 + 3 ^ 40 * 7357858 * 2
def baseEnd_7357858 : Nat := 1259372580509792860145611

theorem tailTrace_7357858 : CollatzResearch.WordTrace tailWord_7357858 prefixEnd_7357858 1259372580509792860145611 := by
  unfold tailWord_7357858
  simp only [CollatzResearch.WordTrace]
  refine ⟨67090782044436140736678557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178908752118496375297809485 67090782044436140736678557)
  ·
    refine ⟨25159043266663552776254459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67090782044436140736678557 25159043266663552776254459)
    ·
      refine ⟨37738564899995329164381689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25159043266663552776254459 37738564899995329164381689)
      ·
        refine ⟨28303923674996496873286267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37738564899995329164381689 28303923674996496873286267)
        ·
          refine ⟨42455885512494745309929401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28303923674996496873286267 42455885512494745309929401)
          ·
            refine ⟨31841914134371058982447051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42455885512494745309929401 31841914134371058982447051)
            ·
              refine ⟨47762871201556588473670577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31841914134371058982447051 47762871201556588473670577)
              ·
                refine ⟨35822153401167441355252933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47762871201556588473670577 35822153401167441355252933)
                ·
                  refine ⟨6716653762718895254109925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35822153401167441355252933 6716653762718895254109925)
                  ·
                    refine ⟨1259372580509792860145611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6716653762718895254109925 1259372580509792860145611)
                    ·
                      rfl

theorem cell23_7357858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_7357858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357858 prefixEnd_7357858 := by exact prefixLift 7357858
  have htrace : WordTrace (prefixWord ++ tailWord_7357858) baseStart_7357858 baseEnd_7357858 := by
    simpa [prefixWord, tailWord_7357858, baseEnd_7357858] using wordTrace_append hprefix tailTrace_7357858
  have hstable : (prefixWord ++ tailWord_7357858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357858).length < 2 ^ (prefixWord ++ tailWord_7357858).sum := by decide
  have hdescent : baseEnd_7357858 < baseStart_7357858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357868 : List Nat := [2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 3]
def baseStart_7357868 : Nat := 118140960795 + 7357868 * 2 ^ 59
def prefixEnd_7357868 : Nat := 4983230072969 + 3 ^ 40 * 7357868 * 2
def baseEnd_7357868 : Nat := 3778122876335923541311787

theorem tailTrace_7357868 : CollatzResearch.WordTrace tailWord_7357868 prefixEnd_7357868 3778122876335923541311787 := by
  unfold tailWord_7357868
  simp only [CollatzResearch.WordTrace]
  refine ⟨134181746453854167327289129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178908995271805556436385505 134181746453854167327289129)
  ·
    refine ⟨100636309840390625495466847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134181746453854167327289129 100636309840390625495466847)
    ·
      refine ⟨150954464760585938243200271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100636309840390625495466847 150954464760585938243200271)
      ·
        refine ⟨226431697140878907364800407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150954464760585938243200271 226431697140878907364800407)
        ·
          refine ⟨339647545711318361047200611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226431697140878907364800407 339647545711318361047200611)
          ·
            refine ⟨509471318566977541570800917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339647545711318361047200611 509471318566977541570800917)
            ·
              refine ⟨23881468057827072261131293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 509471318566977541570800917 23881468057827072261131293)
              ·
                refine ⟨8955550521685152097924235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23881468057827072261131293 8955550521685152097924235)
                ·
                  refine ⟨13433325782527728146886353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8955550521685152097924235 13433325782527728146886353)
                  ·
                    refine ⟨10074994336895796110164765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13433325782527728146886353 10074994336895796110164765)
                    ·
                      refine ⟨3778122876335923541311787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10074994336895796110164765 3778122876335923541311787)
                      ·
                        rfl

theorem cell23_7357868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_7357868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357868 prefixEnd_7357868 := by exact prefixLift 7357868
  have htrace : WordTrace (prefixWord ++ tailWord_7357868) baseStart_7357868 baseEnd_7357868 := by
    simpa [prefixWord, tailWord_7357868, baseEnd_7357868] using wordTrace_append hprefix tailTrace_7357868
  have hstable : (prefixWord ++ tailWord_7357868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357868).length < 2 ^ (prefixWord ++ tailWord_7357868).sum := by decide
  have hdescent : baseEnd_7357868 < baseStart_7357868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357892 : List Nat := [2, 3, 3, 2, 1, 1, 4, 1, 2, 4]
def baseStart_7357892 : Nat := 118140960795 + 7357892 * 2 ^ 59
def prefixEnd_7357892 : Nat := 4983230072969 + 3 ^ 40 * 7357892 * 2
def baseEnd_7357892 : Nat := 1259378399957210482470559

theorem tailTrace_7357892 : CollatzResearch.WordTrace tailWord_7357892 prefixEnd_7357892 1259378399957210482470559 := by
  unfold tailWord_7357892
  simp only [CollatzResearch.WordTrace]
  refine ⟨134182184129810693376725965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178909578839747591168967953 134182184129810693376725965)
  ·
    refine ⟨50318319048679010016272237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134182184129810693376725965 50318319048679010016272237)
    ·
      refine ⟨18869369643254628756102089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50318319048679010016272237 18869369643254628756102089)
      ·
        refine ⟨14152027232440971567076567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18869369643254628756102089 14152027232440971567076567)
        ·
          refine ⟨21228040848661457350614851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14152027232440971567076567 21228040848661457350614851)
          ·
            refine ⟨31842061272992186025922277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21228040848661457350614851 31842061272992186025922277)
            ·
              refine ⟨5970386488686034879860427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31842061272992186025922277 5970386488686034879860427)
              ·
                refine ⟨8955579733029052319790641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5970386488686034879860427 8955579733029052319790641)
                ·
                  refine ⟨6716684799771789239842981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8955579733029052319790641 6716684799771789239842981)
                  ·
                    refine ⟨1259378399957210482470559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6716684799771789239842981 1259378399957210482470559)
                    ·
                      rfl

theorem cell23_7357892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_7357892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357892 prefixEnd_7357892 := by exact prefixLift 7357892
  have htrace : WordTrace (prefixWord ++ tailWord_7357892) baseStart_7357892 baseEnd_7357892 := by
    simpa [prefixWord, tailWord_7357892, baseEnd_7357892] using wordTrace_append hprefix tailTrace_7357892
  have hstable : (prefixWord ++ tailWord_7357892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357892).length < 2 ^ (prefixWord ++ tailWord_7357892).sum := by decide
  have hdescent : baseEnd_7357892 < baseStart_7357892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357933 : List Nat := [1, 5, 1, 3, 2, 2, 2, 2, 1, 2, 2]
def baseStart_7357933 : Nat := 118140960795 + 7357933 * 2 ^ 59
def prefixEnd_7357933 : Nat := 4983230072969 + 3 ^ 40 * 7357933 * 2
def baseEnd_7357933 : Nat := 3778156252578465786998989

theorem tailTrace_7357933 : CollatzResearch.WordTrace tailWord_7357933 prefixEnd_7357933 3778156252578465786998989 := by
  unfold tailWord_7357933
  simp only [CollatzResearch.WordTrace]
  refine ⟨268365863652472850755694453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178910575768315233837129635 268365863652472850755694453)
  ·
    refine ⟨25159299717419329758346355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268365863652472850755694453 25159299717419329758346355)
    ·
      refine ⟨37738949576128994637519533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25159299717419329758346355 37738949576128994637519533)
      ·
        refine ⟨14152106091048372989069825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37738949576128994637519533 14152106091048372989069825)
        ·
          refine ⟨10614079568286279741802369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14152106091048372989069825 10614079568286279741802369)
          ·
            refine ⟨7960559676214709806351777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10614079568286279741802369 7960559676214709806351777)
            ·
              refine ⟨5970419757161032354763833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7960559676214709806351777 5970419757161032354763833)
              ·
                refine ⟨4477814817870774266072875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5970419757161032354763833 4477814817870774266072875)
                ·
                  refine ⟨6716722226806161399109313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4477814817870774266072875 6716722226806161399109313)
                  ·
                    refine ⟨5037541670104621049331985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6716722226806161399109313 5037541670104621049331985)
                    ·
                      refine ⟨3778156252578465786998989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5037541670104621049331985 3778156252578465786998989)
                      ·
                        rfl

theorem cell23_7357933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_7357933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357933 prefixEnd_7357933 := by exact prefixLift 7357933
  have htrace : WordTrace (prefixWord ++ tailWord_7357933) baseStart_7357933 baseEnd_7357933 := by
    simpa [prefixWord, tailWord_7357933, baseEnd_7357933] using wordTrace_append hprefix tailTrace_7357933
  have hstable : (prefixWord ++ tailWord_7357933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357933).length < 2 ^ (prefixWord ++ tailWord_7357933).sum := by decide
  have hdescent : baseEnd_7357933 < baseStart_7357933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357938 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_7357938 : Nat := 118140960795 + 7357938 * 2 ^ 59
def prefixEnd_7357938 : Nat := 4983230072969 + 3 ^ 40 * 7357938 * 2
def baseEnd_7357938 : Nat := 3778158819981738267436465

theorem tailTrace_7357938 : CollatzResearch.WordTrace tailWord_7357938 prefixEnd_7357938 3778158819981738267436465 := by
  unfold tailWord_7357938
  simp only [CollatzResearch.WordTrace]
  refine ⟨67091511504363684152406617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178910697344969824406417645 67091511504363684152406617)
  ·
    refine ⟨50318633628272763114304963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67091511504363684152406617 50318633628272763114304963)
    ·
      refine ⟨75477950442409144671457445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50318633628272763114304963 75477950442409144671457445)
      ·
        refine ⟨14152115707951714625898271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75477950442409144671457445 14152115707951714625898271)
        ·
          refine ⟨21228173561927571938847407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14152115707951714625898271 21228173561927571938847407)
          ·
            refine ⟨31842260342891357908271111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21228173561927571938847407 31842260342891357908271111)
            ·
              refine ⟨47763390514337036862406667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31842260342891357908271111 47763390514337036862406667)
              ·
                refine ⟨71645085771505555293610001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47763390514337036862406667 71645085771505555293610001)
                ·
                  refine ⟨53733814328629166470207501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71645085771505555293610001 53733814328629166470207501)
                  ·
                    refine ⟨20150180373235937426327813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53733814328629166470207501 20150180373235937426327813)
                    ·
                      refine ⟨3778158819981738267436465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20150180373235937426327813 3778158819981738267436465)
                      ·
                        rfl

theorem cell23_7357938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_7357938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357938 prefixEnd_7357938 := by exact prefixLift 7357938
  have htrace : WordTrace (prefixWord ++ tailWord_7357938) baseStart_7357938 baseEnd_7357938 := by
    simpa [prefixWord, tailWord_7357938, baseEnd_7357938] using wordTrace_append hprefix tailTrace_7357938
  have hstable : (prefixWord ++ tailWord_7357938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357938).length < 2 ^ (prefixWord ++ tailWord_7357938).sum := by decide
  have hdescent : baseEnd_7357938 < baseStart_7357938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357961 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 7]
def baseStart_7357961 : Nat := 118140960795 + 7357961 * 2 ^ 59
def prefixEnd_7357961 : Nat := 4983230072969 + 3 ^ 40 * 7357961 * 2
def baseEnd_7357961 : Nat := 419796736670754630827651

theorem tailTrace_7357961 : CollatzResearch.WordTrace tailWord_7357961 prefixEnd_7357961 419796736670754630827651 := by
  unfold tailWord_7357961
  simp only [CollatzResearch.WordTrace]
  refine ⟨268366884896371411537713737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178911256597580941025142491 268366884896371411537713737)
  ·
    refine ⟨201275163672278558653285303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268366884896371411537713737 201275163672278558653285303)
    ·
      refine ⟨301912745508417837979927955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201275163672278558653285303 301912745508417837979927955)
      ·
        refine ⟨452869118262626756969891933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301912745508417837979927955 452869118262626756969891933)
        ·
          refine ⟨169825919348485033863709475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 452869118262626756969891933 169825919348485033863709475)
          ·
            refine ⟨254738879022727550795564213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169825919348485033863709475 254738879022727550795564213)
            ·
              refine ⟨23881769908380707887084145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254738879022727550795564213 23881769908380707887084145)
              ·
                refine ⟨17911327431285530915313109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23881769908380707887084145 17911327431285530915313109)
                ·
                  refine ⟨419796736670754630827651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17911327431285530915313109 419796736670754630827651)
                  ·
                    rfl

theorem cell23_7357961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 7].length) (baseStart_7357961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357961 prefixEnd_7357961 := by exact prefixLift 7357961
  have htrace : WordTrace (prefixWord ++ tailWord_7357961) baseStart_7357961 baseEnd_7357961 := by
    simpa [prefixWord, tailWord_7357961, baseEnd_7357961] using wordTrace_append hprefix tailTrace_7357961
  have hstable : (prefixWord ++ tailWord_7357961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357961).length < 2 ^ (prefixWord ++ tailWord_7357961).sum := by decide
  have hdescent : baseEnd_7357961 < baseStart_7357961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7357976 : List Nat := [2, 1, 2, 3, 5, 1, 2, 1, 1, 3, 2]
def baseStart_7357976 : Nat := 118140960795 + 7357976 * 2 ^ 59
def prefixEnd_7357976 : Nat := 4983230072969 + 3 ^ 40 * 7357976 * 2
def baseEnd_7357976 : Nat := 3778178332246609118761291

theorem tailTrace_7357976 : CollatzResearch.WordTrace tailWord_7357976 prefixEnd_7357976 3778178332246609118761291 := by
  unfold tailWord_7357976
  simp only [CollatzResearch.WordTrace]
  refine ⟨134183715995658534549754891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178911621327544712733006521 134183715995658534549754891)
  ·
    refine ⟨201275573993487801824632337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134183715995658534549754891 201275573993487801824632337)
    ·
      refine ⟨150956680495115851368474253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201275573993487801824632337 150956680495115851368474253)
      ·
        refine ⟨56608755185668444263177845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150956680495115851368474253 56608755185668444263177845)
        ·
          refine ⟨5307070798656416649672923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56608755185668444263177845 5307070798656416649672923)
          ·
            refine ⟨7960606197984624974509385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307070798656416649672923 7960606197984624974509385)
            ·
              refine ⟨5970454648488468730882039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7960606197984624974509385 5970454648488468730882039)
              ·
                refine ⟨8955681972732703096323059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5970454648488468730882039 8955681972732703096323059)
                ·
                  refine ⟨13433522959099054644484589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8955681972732703096323059 13433522959099054644484589)
                  ·
                    refine ⟨5037571109662145491681721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13433522959099054644484589 5037571109662145491681721)
                    ·
                      refine ⟨3778178332246609118761291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5037571109662145491681721 3778178332246609118761291)
                      ·
                        rfl

theorem cell23_7357976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_7357976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7357976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7357976 prefixEnd_7357976 := by exact prefixLift 7357976
  have htrace : WordTrace (prefixWord ++ tailWord_7357976) baseStart_7357976 baseEnd_7357976 := by
    simpa [prefixWord, tailWord_7357976, baseEnd_7357976] using wordTrace_append hprefix tailTrace_7357976
  have hstable : (prefixWord ++ tailWord_7357976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7357976).length < 2 ^ (prefixWord ++ tailWord_7357976).sum := by decide
  have hdescent : baseEnd_7357976 < baseStart_7357976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7357976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358001 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_7358001 : Nat := 118140960795 + 7358001 * 2 ^ 59
def prefixEnd_7358001 : Nat := 4983230072969 + 3 ^ 40 * 7358001 * 2
def baseEnd_7358001 : Nat := 3778191169262971520948675

theorem tailTrace_7358001 : CollatzResearch.WordTrace tailWord_7358001 prefixEnd_7358001 3778191169262971520948675 := by
  unfold tailWord_7358001
  simp only [CollatzResearch.WordTrace]
  refine ⟨268368343816226498369169857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178912229210817665579446571 268368343816226498369169857)
  ·
    refine ⟨201276257862169873776877393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268368343816226498369169857 201276257862169873776877393)
    ·
      refine ⟨150957193396627405332658045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201276257862169873776877393 150957193396627405332658045)
      ·
        refine ⟨56608947523735276999746767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150957193396627405332658045 56608947523735276999746767)
        ·
          refine ⟨84913421285602915499620151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56608947523735276999746767 84913421285602915499620151)
          ·
            refine ⟨127370131928404373249430227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84913421285602915499620151 127370131928404373249430227)
            ·
              refine ⟨191055197892606559874145341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127370131928404373249430227 191055197892606559874145341)
              ·
                refine ⟨71645699209727459952804503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191055197892606559874145341 71645699209727459952804503)
                ·
                  refine ⟨107468548814591189929206755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71645699209727459952804503 107468548814591189929206755)
                  ·
                    refine ⟨161202823221886784893810133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107468548814591189929206755 161202823221886784893810133)
                    ·
                      refine ⟨3778191169262971520948675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161202823221886784893810133 3778191169262971520948675)
                      ·
                        rfl

theorem cell23_7358001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_7358001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358001 prefixEnd_7358001 := by exact prefixLift 7358001
  have htrace : WordTrace (prefixWord ++ tailWord_7358001) baseStart_7358001 baseEnd_7358001 := by
    simpa [prefixWord, tailWord_7358001, baseEnd_7358001] using wordTrace_append hprefix tailTrace_7358001
  have hstable : (prefixWord ++ tailWord_7358001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358001).length < 2 ^ (prefixWord ++ tailWord_7358001).sum := by decide
  have hdescent : baseEnd_7358001 < baseStart_7358001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358006 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_7358006 : Nat := 118140960795 + 7358006 * 2 ^ 59
def prefixEnd_7358006 : Nat := 4983230072969 + 3 ^ 40 * 7358006 * 2
def baseEnd_7358006 : Nat := 3778193736666244001386153

theorem tailTrace_7358006 : CollatzResearch.WordTrace tailWord_7358006 prefixEnd_7358006 3778193736666244001386153 := by
  unfold tailWord_7358006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16773032886325524013943867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178912350787472256148734581 16773032886325524013943867)
  ·
    refine ⟨25159549329488286020915801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16773032886325524013943867 25159549329488286020915801)
    ·
      refine ⟨18869661997116214515686851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25159549329488286020915801 18869661997116214515686851)
      ·
        refine ⟨28304492995674321773530277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18869661997116214515686851 28304492995674321773530277)
        ·
          refine ⟨5307092436688935332536927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28304492995674321773530277 5307092436688935332536927)
          ·
            refine ⟨7960638655033402998805391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307092436688935332536927 7960638655033402998805391)
            ·
              refine ⟨11940957982550104498208087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7960638655033402998805391 11940957982550104498208087)
              ·
                refine ⟨17911436973825156747312131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11940957982550104498208087 17911436973825156747312131)
                ·
                  refine ⟨26867155460737735120968197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17911436973825156747312131 26867155460737735120968197)
                  ·
                    refine ⟨5037591648888325335181537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26867155460737735120968197 5037591648888325335181537)
                    ·
                      refine ⟨3778193736666244001386153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5037591648888325335181537 3778193736666244001386153)
                      ·
                        rfl

theorem cell23_7358006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_7358006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358006 prefixEnd_7358006 := by exact prefixLift 7358006
  have htrace : WordTrace (prefixWord ++ tailWord_7358006) baseStart_7358006 baseEnd_7358006 := by
    simpa [prefixWord, tailWord_7358006, baseEnd_7358006] using wordTrace_append hprefix tailTrace_7358006
  have hstable : (prefixWord ++ tailWord_7358006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358006).length < 2 ^ (prefixWord ++ tailWord_7358006).sum := by decide
  have hdescent : baseEnd_7358006 < baseStart_7358006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358021 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 2, 8]
def baseStart_7358021 : Nat := 118140960795 + 7358021 * 2 ^ 59
def prefixEnd_7358021 : Nat := 4983230072969 + 3 ^ 40 * 7358021 * 2
def baseEnd_7358021 : Nat := 1259400479625353814232861

theorem tailTrace_7358021 : CollatzResearch.WordTrace tailWord_7358021 prefixEnd_7358021 1259400479625353814232861 := by
  unfold tailWord_7358021
  simp only [CollatzResearch.WordTrace]
  refine ⟨268369073276154041784897917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178912715517436027856598611 268369073276154041784897917)
  ·
    refine ⟨100638402478557765669336719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268369073276154041784897917 100638402478557765669336719)
    ·
      refine ⟨150957603717836648504005079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100638402478557765669336719 150957603717836648504005079)
      ·
        refine ⟨226436405576754972756007619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150957603717836648504005079 226436405576754972756007619)
        ·
          refine ⟨339654608365132459134011429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226436405576754972756007619 339654608365132459134011429)
          ·
            refine ⟨63685239068462336087627143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339654608365132459134011429 63685239068462336087627143)
            ·
              refine ⟨95527858602693504131440715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63685239068462336087627143 95527858602693504131440715)
              ·
                refine ⟨143291787904040256197161073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95527858602693504131440715 143291787904040256197161073)
                ·
                  refine ⟨107468840928030192147870805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143291787904040256197161073 107468840928030192147870805)
                  ·
                    refine ⟨1259400479625353814232861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107468840928030192147870805 1259400479625353814232861)
                    ·
                      rfl

theorem cell23_7358021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_7358021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358021 prefixEnd_7358021 := by exact prefixLift 7358021
  have htrace : WordTrace (prefixWord ++ tailWord_7358021) baseStart_7358021 baseEnd_7358021 := by
    simpa [prefixWord, tailWord_7358021, baseEnd_7358021] using wordTrace_append hprefix tailTrace_7358021
  have hstable : (prefixWord ++ tailWord_7358021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358021).length < 2 ^ (prefixWord ++ tailWord_7358021).sum := by decide
  have hdescent : baseEnd_7358021 < baseStart_7358021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358028 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_7358028 : Nat := 118140960795 + 7358028 * 2 ^ 59
def prefixEnd_7358028 : Nat := 4983230072969 + 3 ^ 40 * 7358028 * 2
def baseEnd_7358028 : Nat := 3778205033240642915311051

theorem tailTrace_7358028 : CollatzResearch.WordTrace tailWord_7358028 prefixEnd_7358028 3778205033240642915311051 := by
  unfold tailWord_7358028
  simp only [CollatzResearch.WordTrace]
  refine ⟨134184664293564340990201369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178912885724752454653601825 134184664293564340990201369)
  ·
    refine ⟨100638498220173255742651027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134184664293564340990201369 100638498220173255742651027)
    ·
      refine ⟨150957747330259883613976541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100638498220173255742651027 150957747330259883613976541)
      ·
        refine ⟨56609155248847456355241203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150957747330259883613976541 56609155248847456355241203)
        ·
          refine ⟨84913732873271184532861805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56609155248847456355241203 84913732873271184532861805)
          ·
            refine ⟨31842649827476694199823177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84913732873271184532861805 31842649827476694199823177)
            ·
              refine ⟨23881987370607520649867383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31842649827476694199823177 23881987370607520649867383)
              ·
                refine ⟨35822981055911280974801075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23881987370607520649867383 35822981055911280974801075)
                ·
                  refine ⟨53734471583866921462201613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35822981055911280974801075 53734471583866921462201613)
                  ·
                    refine ⟨20150426843950095548325605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53734471583866921462201613 20150426843950095548325605)
                    ·
                      refine ⟨3778205033240642915311051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20150426843950095548325605 3778205033240642915311051)
                      ·
                        rfl

theorem cell23_7358028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_7358028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358028 prefixEnd_7358028 := by exact prefixLift 7358028
  have htrace : WordTrace (prefixWord ++ tailWord_7358028) baseStart_7358028 baseEnd_7358028 := by
    simpa [prefixWord, tailWord_7358028, baseEnd_7358028] using wordTrace_append hprefix tailTrace_7358028
  have hstable : (prefixWord ++ tailWord_7358028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358028).length < 2 ^ (prefixWord ++ tailWord_7358028).sum := by decide
  have hdescent : baseEnd_7358028 < baseStart_7358028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358029 : List Nat := [1, 6, 1, 1, 3, 2, 1, 3, 5]
def baseStart_7358029 : Nat := 118140960795 + 7358029 * 2 ^ 59
def prefixEnd_7358029 : Nat := 4983230072969 + 3 ^ 40 * 7358029 * 2
def baseEnd_7358029 : Nat := 419800616302366379044283

theorem tailTrace_7358029 : CollatzResearch.WordTrace tailWord_7358029 prefixEnd_7358029 419800616302366379044283 := by
  unfold tailWord_7358029
  simp only [CollatzResearch.WordTrace]
  refine ⟨268369365060125059151189141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178912910040083372767459427 268369365060125059151189141)
  ·
    refine ⟨12579813987193362147711991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 268369365060125059151189141 12579813987193362147711991)
    ·
      refine ⟨18869720980790043221567987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12579813987193362147711991 18869720980790043221567987)
      ·
        refine ⟨28304581471185064832351981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18869720980790043221567987 28304581471185064832351981)
        ·
          refine ⟨10614218051694399312131993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28304581471185064832351981 10614218051694399312131993)
          ·
            refine ⟨7960663538770799484098995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10614218051694399312131993 7960663538770799484098995)
            ·
              refine ⟨11940995308156199226148493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7960663538770799484098995 11940995308156199226148493)
              ·
                refine ⟨4477873240558574709805685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11940995308156199226148493 4477873240558574709805685)
                ·
                  refine ⟨419800616302366379044283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4477873240558574709805685 419800616302366379044283)
                  ·
                    rfl

theorem cell23_7358029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_7358029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358029 prefixEnd_7358029 := by exact prefixLift 7358029
  have htrace : WordTrace (prefixWord ++ tailWord_7358029) baseStart_7358029 baseEnd_7358029 := by
    simpa [prefixWord, tailWord_7358029, baseEnd_7358029] using wordTrace_append hprefix tailTrace_7358029
  have hstable : (prefixWord ++ tailWord_7358029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358029).length < 2 ^ (prefixWord ++ tailWord_7358029).sum := by decide
  have hdescent : baseEnd_7358029 < baseStart_7358029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358031 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 5]
def baseStart_7358031 : Nat := 118140960795 + 7358031 * 2 ^ 59
def prefixEnd_7358031 : Nat := 4983230072969 + 3 ^ 40 * 7358031 * 2
def baseEnd_7358031 : Nat := 3778206573682606403573537

theorem tailTrace_7358031 : CollatzResearch.WordTrace tailWord_7358031 prefixEnd_7358031 3778206573682606403573537 := by
  unfold tailWord_7358031
  simp only [CollatzResearch.WordTrace]
  refine ⟨268369438006117813492761947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178912958670745208995174631 268369438006117813492761947)
  ·
    refine ⟨402554157009176720239142921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268369438006117813492761947 402554157009176720239142921)
    ·
      refine ⟨301915617756882540179357191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402554157009176720239142921 301915617756882540179357191)
      ·
        refine ⟨452873426635323810269035787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301915617756882540179357191 452873426635323810269035787)
        ·
          refine ⟨679310139952985715403553681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452873426635323810269035787 679310139952985715403553681)
          ·
            refine ⟨509482604964739286552665261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 679310139952985715403553681 509482604964739286552665261)
            ·
              refine ⟨191055976861777232457249473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 509482604964739286552665261 191055976861777232457249473)
              ·
                refine ⟨143291982646332924342937105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191055976861777232457249473 143291982646332924342937105)
                ·
                  refine ⟨107468986984749693257202829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143291982646332924342937105 107468986984749693257202829)
                  ·
                    refine ⟨40300870119281134971451061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107468986984749693257202829 40300870119281134971451061)
                    ·
                      refine ⟨3778206573682606403573537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40300870119281134971451061 3778206573682606403573537)
                      ·
                        rfl

theorem cell23_7358031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_7358031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358031 prefixEnd_7358031 := by exact prefixLift 7358031
  have htrace : WordTrace (prefixWord ++ tailWord_7358031) baseStart_7358031 baseEnd_7358031 := by
    simpa [prefixWord, tailWord_7358031, baseEnd_7358031] using wordTrace_append hprefix tailTrace_7358031
  have hstable : (prefixWord ++ tailWord_7358031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358031).length < 2 ^ (prefixWord ++ tailWord_7358031).sum := by decide
  have hdescent : baseEnd_7358031 < baseStart_7358031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358041 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 6]
def baseStart_7358041 : Nat := 118140960795 + 7358041 * 2 ^ 59
def prefixEnd_7358041 : Nat := 4983230072969 + 3 ^ 40 * 7358041 * 2
def baseEnd_7358041 : Nat := 3778211708489151364448491

theorem tailTrace_7358041 : CollatzResearch.WordTrace tailWord_7358041 prefixEnd_7358041 3778211708489151364448491 := by
  unfold tailWord_7358041
  simp only [CollatzResearch.WordTrace]
  refine ⟨268369802736081585200625977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178913201824054390133750651 268369802736081585200625977)
  ·
    refine ⟨201277352052061188900469483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268369802736081585200625977 201277352052061188900469483)
    ·
      refine ⟨301916028078091783350704225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201277352052061188900469483 301916028078091783350704225)
      ·
        refine ⟨226437021058568837513028169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301916028078091783350704225 226437021058568837513028169)
        ·
          refine ⟨169827765793926628134771127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226437021058568837513028169 169827765793926628134771127)
          ·
            refine ⟨254741648690889942202156691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169827765793926628134771127 254741648690889942202156691)
            ·
              refine ⟨382112473036334913303235037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254741648690889942202156691 382112473036334913303235037)
              ·
                refine ⟨143292177388625592488713139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382112473036334913303235037 143292177388625592488713139)
                ·
                  refine ⟨214938266082938388733069709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143292177388625592488713139 214938266082938388733069709)
                  ·
                    refine ⟨80601849781101895774901141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214938266082938388733069709 80601849781101895774901141)
                    ·
                      refine ⟨3778211708489151364448491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80601849781101895774901141 3778211708489151364448491)
                      ·
                        rfl

theorem cell23_7358041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_7358041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358041 prefixEnd_7358041 := by exact prefixLift 7358041
  have htrace : WordTrace (prefixWord ++ tailWord_7358041) baseStart_7358041 baseEnd_7358041 := by
    simpa [prefixWord, tailWord_7358041, baseEnd_7358041] using wordTrace_append hprefix tailTrace_7358041
  have hstable : (prefixWord ++ tailWord_7358041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358041).length < 2 ^ (prefixWord ++ tailWord_7358041).sum := by decide
  have hdescent : baseEnd_7358041 < baseStart_7358041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358055 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 3, 4]
def baseStart_7358055 : Nat := 118140960795 + 7358055 * 2 ^ 59
def prefixEnd_7358055 : Nat := 4983230072969 + 3 ^ 40 * 7358055 * 2
def baseEnd_7358055 : Nat := 1259406299072771436557809

theorem tailTrace_7358055 : CollatzResearch.WordTrace tailWord_7358055 prefixEnd_7358055 1259406299072771436557809 := by
  unfold tailWord_7358055
  simp only [CollatzResearch.WordTrace]
  refine ⟨268370313358030865591635619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178913542238687243727757079 268370313358030865591635619)
  ·
    refine ⟨402555470037046298387453429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268370313358030865591635619 402555470037046298387453429)
    ·
      refine ⟨37739575315973090473823759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 402555470037046298387453429 37739575315973090473823759)
      ·
        refine ⟨56609362973959635710735639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37739575315973090473823759 56609362973959635710735639)
        ·
          refine ⟨84914044460939453566103459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56609362973959635710735639 84914044460939453566103459)
          ·
            refine ⟨127371066691409180349155189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84914044460939453566103459 127371066691409180349155189)
            ·
              refine ⟨11941037502319610657733299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127371066691409180349155189 11941037502319610657733299)
              ·
                refine ⟨17911556253479415986599949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11941037502319610657733299 17911556253479415986599949)
                ·
                  refine ⟨6716833595054780994974981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17911556253479415986599949 6716833595054780994974981)
                  ·
                    refine ⟨1259406299072771436557809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6716833595054780994974981 1259406299072771436557809)
                    ·
                      rfl

theorem cell23_7358055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_7358055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358055 prefixEnd_7358055 := by exact prefixLift 7358055
  have htrace : WordTrace (prefixWord ++ tailWord_7358055) baseStart_7358055 baseEnd_7358055 := by
    simpa [prefixWord, tailWord_7358055, baseEnd_7358055] using wordTrace_append hprefix tailTrace_7358055
  have hstable : (prefixWord ++ tailWord_7358055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358055).length < 2 ^ (prefixWord ++ tailWord_7358055).sum := by decide
  have hdescent : baseEnd_7358055 < baseStart_7358055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358105 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 4, 3, 2]
def baseStart_7358105 : Nat := 118140960795 + 7358105 * 2 ^ 59
def prefixEnd_7358105 : Nat := 4983230072969 + 3 ^ 40 * 7358105 * 2
def baseEnd_7358105 : Nat := 3778244571251039114048197

theorem tailTrace_7358105 : CollatzResearch.WordTrace tailWord_7358105 prefixEnd_7358105 3778244571251039114048197 := by
  unfold tailWord_7358105
  simp only [CollatzResearch.WordTrace]
  refine ⟨268372137007849724130955769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178914758005233149420637179 268372137007849724130955769)
  ·
    refine ⟨201279102755887293098216827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268372137007849724130955769 201279102755887293098216827)
    ·
      refine ⟨301918654133830939647325241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201279102755887293098216827 301918654133830939647325241)
      ·
        refine ⟨226438990600373204735493931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301918654133830939647325241 226438990600373204735493931)
        ·
          refine ⟨339658485900559807103240897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226438990600373204735493931 339658485900559807103240897)
          ·
            refine ⟨254743864425419855327430673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339658485900559807103240897 254743864425419855327430673)
            ·
              refine ⟨191057898319064891495573005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254743864425419855327430673 191057898319064891495573005)
              ·
                refine ⟨71646711869649334310839877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191057898319064891495573005 71646711869649334310839877)
                ·
                  refine ⟨13433758475559250183282477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71646711869649334310839877 13433758475559250183282477)
                  ·
                    refine ⟨5037659428334718818730929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13433758475559250183282477 5037659428334718818730929)
                    ·
                      refine ⟨3778244571251039114048197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5037659428334718818730929 3778244571251039114048197)
                      ·
                        rfl

theorem cell23_7358105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 3, 2].length) (baseStart_7358105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358105 prefixEnd_7358105 := by exact prefixLift 7358105
  have htrace : WordTrace (prefixWord ++ tailWord_7358105) baseStart_7358105 baseEnd_7358105 := by
    simpa [prefixWord, tailWord_7358105, baseEnd_7358105] using wordTrace_append hprefix tailTrace_7358105
  have hstable : (prefixWord ++ tailWord_7358105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358105).length < 2 ^ (prefixWord ++ tailWord_7358105).sum := by decide
  have hdescent : baseEnd_7358105 < baseStart_7358105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358128 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 1, 6]
def baseStart_7358128 : Nat := 118140960795 + 7358128 * 2 ^ 59
def prefixEnd_7358128 : Nat := 4983230072969 + 3 ^ 40 * 7358128 * 2
def baseEnd_7358128 : Nat := 1259418793768697508020197

theorem tailTrace_7358128 : CollatzResearch.WordTrace tailWord_7358128 prefixEnd_7358128 1259418793768697508020197 := by
  unfold tailWord_7358128
  simp only [CollatzResearch.WordTrace]
  refine ⟨134186487943383199529521519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178915317257844266039362025 134186487943383199529521519)
  ·
    refine ⟨201279731915074799294282279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134186487943383199529521519 201279731915074799294282279)
    ·
      refine ⟨301919597872612198941423419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201279731915074799294282279 301919597872612198941423419)
      ·
        refine ⟨452879396808918298412135129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301919597872612198941423419 452879396808918298412135129)
        ·
          refine ⟨339659547606688723809101347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452879396808918298412135129 339659547606688723809101347)
          ·
            refine ⟨509489321410033085713652021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339659547606688723809101347 509489321410033085713652021)
            ·
              refine ⟨47764623882190601785654877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 509489321410033085713652021 47764623882190601785654877)
              ·
                refine ⟨17911733955821475669620579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47764623882190601785654877 17911733955821475669620579)
                ·
                  refine ⟨26867600933732213504430869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17911733955821475669620579 26867600933732213504430869)
                  ·
                    refine ⟨1259418793768697508020197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26867600933732213504430869 1259418793768697508020197)
                    ·
                      rfl

theorem cell23_7358128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 1, 6].length) (baseStart_7358128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358128 prefixEnd_7358128 := by exact prefixLift 7358128
  have htrace : WordTrace (prefixWord ++ tailWord_7358128) baseStart_7358128 baseEnd_7358128 := by
    simpa [prefixWord, tailWord_7358128, baseEnd_7358128] using wordTrace_append hprefix tailTrace_7358128
  have hstable : (prefixWord ++ tailWord_7358128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358128).length < 2 ^ (prefixWord ++ tailWord_7358128).sum := by decide
  have hdescent : baseEnd_7358128 < baseStart_7358128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358135 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 4]
def baseStart_7358135 : Nat := 118140960795 + 7358135 * 2 ^ 59
def prefixEnd_7358135 : Nat := 4983230072969 + 3 ^ 40 * 7358135 * 2
def baseEnd_7358135 : Nat := 3778259975670673996673059

theorem tailTrace_7358135 : CollatzResearch.WordTrace tailWord_7358135 prefixEnd_7358135 3778259975670673996673059 := by
  unfold tailWord_7358135
  simp only [CollatzResearch.WordTrace]
  refine ⟨268373231197741039254547859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178915487465160692836365239 268373231197741039254547859)
  ·
    refine ⟨402559846796611558881821789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268373231197741039254547859 402559846796611558881821789)
    ·
      refine ⟨150959942548729334580683171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402559846796611558881821789 150959942548729334580683171)
      ·
        refine ⟨226439913823094001871024757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150959942548729334580683171 226439913823094001871024757)
        ·
          refine ⟨21228741920915062675408571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226439913823094001871024757 21228741920915062675408571)
          ·
            refine ⟨31843112881372594013112857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21228741920915062675408571 31843112881372594013112857)
            ·
              refine ⟨23882334661029445509834643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31843112881372594013112857 23882334661029445509834643)
              ·
                refine ⟨35823501991544168264751965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23882334661029445509834643 35823501991544168264751965)
                ·
                  refine ⟨13433813246829063099281987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35823501991544168264751965 13433813246829063099281987)
                  ·
                    refine ⟨20150719870243594648922981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13433813246829063099281987 20150719870243594648922981)
                    ·
                      refine ⟨3778259975670673996673059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20150719870243594648922981 3778259975670673996673059)
                      ·
                        rfl

theorem cell23_7358135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_7358135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358135 prefixEnd_7358135 := by exact prefixLift 7358135
  have htrace : WordTrace (prefixWord ++ tailWord_7358135) baseStart_7358135 baseEnd_7358135 := by
    simpa [prefixWord, tailWord_7358135, baseEnd_7358135] using wordTrace_append hprefix tailTrace_7358135
  have hstable : (prefixWord ++ tailWord_7358135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358135).length < 2 ^ (prefixWord ++ tailWord_7358135).sum := by decide
  have hdescent : baseEnd_7358135 < baseStart_7358135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358152 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 5, 2, 2]
def baseStart_7358152 : Nat := 118140960795 + 7358152 * 2 ^ 59
def prefixEnd_7358152 : Nat := 4983230072969 + 3 ^ 40 * 7358152 * 2
def baseEnd_7358152 : Nat := 3778268704841800430160481

theorem tailTrace_7358152 : CollatzResearch.WordTrace tailWord_7358152 prefixEnd_7358152 3778268704841800430160481 := by
  unfold tailWord_7358152
  simp only [CollatzResearch.WordTrace]
  refine ⟨134186925619339725578958355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178915900825786300771944473 134186925619339725578958355)
  ·
    refine ⟨201280388429009588368437533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134186925619339725578958355 201280388429009588368437533)
    ·
      refine ⟨75480145660878595638164075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201280388429009588368437533 75480145660878595638164075)
      ·
        refine ⟨113220218491317893457246113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75480145660878595638164075 113220218491317893457246113)
        ·
          refine ⟨84915163868488420092934585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113220218491317893457246113 84915163868488420092934585)
          ·
            refine ⟨63686372901366315069700939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84915163868488420092934585 63686372901366315069700939)
            ·
              refine ⟨95529559352049472604551409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63686372901366315069700939 95529559352049472604551409)
              ·
                refine ⟨71647169514037104453413557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95529559352049472604551409 71647169514037104453413557)
                ·
                  refine ⟨6716922141940978542507521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71647169514037104453413557 6716922141940978542507521)
                  ·
                    refine ⟨5037691606455733906880641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6716922141940978542507521 5037691606455733906880641)
                    ·
                      refine ⟨3778268704841800430160481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5037691606455733906880641 3778268704841800430160481)
                      ·
                        rfl

theorem cell23_7358152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_7358152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358152 prefixEnd_7358152 := by exact prefixLift 7358152
  have htrace : WordTrace (prefixWord ++ tailWord_7358152) baseStart_7358152 baseEnd_7358152 := by
    simpa [prefixWord, tailWord_7358152, baseEnd_7358152] using wordTrace_append hprefix tailTrace_7358152
  have hstable : (prefixWord ++ tailWord_7358152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358152).length < 2 ^ (prefixWord ++ tailWord_7358152).sum := by decide
  have hdescent : baseEnd_7358152 < baseStart_7358152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358158 : List Nat := [4, 1, 1, 1, 3, 1, 12]
def baseStart_7358158 : Nat := 118140960795 + 7358158 * 2 ^ 59
def prefixEnd_7358158 : Nat := 4983230072969 + 3 ^ 40 * 7358158 * 2
def baseEnd_7358158 : Nat := 46645330687971943292413

theorem tailTrace_7358158 : CollatzResearch.WordTrace tailWord_7358158 prefixEnd_7358158 46645330687971943292413 := by
  unfold tailWord_7358158
  simp only [CollatzResearch.WordTrace]
  refine ⟨33546758759582214272829391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178916046717771809455090085 33546758759582214272829391)
  ·
    refine ⟨50320138139373321409244087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33546758759582214272829391 50320138139373321409244087)
    ·
      refine ⟨75480207209059982113866131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50320138139373321409244087 75480207209059982113866131)
      ·
        refine ⟨113220310813589973170799197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75480207209059982113866131 113220310813589973170799197)
        ·
          refine ⟨42457616555096239939049699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113220310813589973170799197 42457616555096239939049699)
          ·
            refine ⟨63686424832644359908574549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42457616555096239939049699 63686424832644359908574549)
            ·
              refine ⟨46645330687971943292413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 63686424832644359908574549 46645330687971943292413)
              ·
                rfl

theorem cell23_7358158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 12].length) (baseStart_7358158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358158 prefixEnd_7358158 := by exact prefixLift 7358158
  have htrace : WordTrace (prefixWord ++ tailWord_7358158) baseStart_7358158 baseEnd_7358158 := by
    simpa [prefixWord, tailWord_7358158, baseEnd_7358158] using wordTrace_append hprefix tailTrace_7358158
  have hstable : (prefixWord ++ tailWord_7358158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358158).length < 2 ^ (prefixWord ++ tailWord_7358158).sum := by decide
  have hdescent : baseEnd_7358158 < baseStart_7358158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358162 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_7358162 : Nat := 118140960795 + 7358162 * 2 ^ 59
def prefixEnd_7358162 : Nat := 4983230072969 + 3 ^ 40 * 7358162 * 2
def baseEnd_7358162 : Nat := 1259424613216115130345145

theorem tailTrace_7358162 : CollatzResearch.WordTrace tailWord_7358162 prefixEnd_7358162 1259424613216115130345145 := by
  unfold tailWord_7358162
  simp only [CollatzResearch.WordTrace]
  refine ⟨67093553992160805716445185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178916143979095481910520493 67093553992160805716445185)
  ·
    refine ⟨50320165494120604287333889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67093553992160805716445185 50320165494120604287333889)
    ·
      refine ⟨37740124120590453215500417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50320165494120604287333889 37740124120590453215500417)
      ·
        refine ⟨28305093090442839911625313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37740124120590453215500417 28305093090442839911625313)
        ·
          refine ⟨21228819817832129933718985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28305093090442839911625313 21228819817832129933718985)
          ·
            refine ⟨15921614863374097450289239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21228819817832129933718985 15921614863374097450289239)
            ·
              refine ⟨23882422295061146175433859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15921614863374097450289239 23882422295061146175433859)
              ·
                refine ⟨35823633442591719263150789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23882422295061146175433859 35823633442591719263150789)
                ·
                  refine ⟨6716931270485947361840773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35823633442591719263150789 6716931270485947361840773)
                  ·
                    refine ⟨1259424613216115130345145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6716931270485947361840773 1259424613216115130345145)
                    ·
                      rfl

theorem cell23_7358162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_7358162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358162 prefixEnd_7358162 := by exact prefixLift 7358162
  have htrace : WordTrace (prefixWord ++ tailWord_7358162) baseStart_7358162 baseEnd_7358162 := by
    simpa [prefixWord, tailWord_7358162, baseEnd_7358162] using wordTrace_append hprefix tailTrace_7358162
  have hstable : (prefixWord ++ tailWord_7358162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358162).length < 2 ^ (prefixWord ++ tailWord_7358162).sum := by decide
  have hdescent : baseEnd_7358162 < baseStart_7358162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358169 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 3, 2, 2]
def baseStart_7358169 : Nat := 118140960795 + 7358169 * 2 ^ 59
def prefixEnd_7358169 : Nat := 4983230072969 + 3 ^ 40 * 7358169 * 2
def baseEnd_7358169 : Nat := 3778277434012926863647903

theorem tailTrace_7358169 : CollatzResearch.WordTrace tailWord_7358169 prefixEnd_7358169 3778277434012926863647903 := by
  unfold tailWord_7358169
  simp only [CollatzResearch.WordTrace]
  refine ⟨268374471279617863061285561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178916314186411908707523707 268374471279617863061285561)
  ·
    refine ⟨201280853459713397295964171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268374471279617863061285561 201280853459713397295964171)
    ·
      refine ⟨301921280189570095943946257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201280853459713397295964171 301921280189570095943946257)
      ·
        refine ⟨226440960142177571957959693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301921280189570095943946257 226440960142177571957959693)
        ·
          refine ⟨84915360053316589484234885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226440960142177571957959693 84915360053316589484234885)
          ·
            refine ⟨15921630009996860528294041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84915360053316589484234885 15921630009996860528294041)
            ·
              refine ⟨11941222507497645396220531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15921630009996860528294041 11941222507497645396220531)
              ·
                refine ⟨17911833761246468094330797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11941222507497645396220531 17911833761246468094330797)
                ·
                  refine ⟨6716937660467425535374049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17911833761246468094330797 6716937660467425535374049)
                  ·
                    refine ⟨5037703245350569151530537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6716937660467425535374049 5037703245350569151530537)
                    ·
                      refine ⟨3778277434012926863647903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5037703245350569151530537 3778277434012926863647903)
                      ·
                        rfl

theorem cell23_7358169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 2, 2].length) (baseStart_7358169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358169 prefixEnd_7358169 := by exact prefixLift 7358169
  have htrace : WordTrace (prefixWord ++ tailWord_7358169) baseStart_7358169 baseEnd_7358169 := by
    simpa [prefixWord, tailWord_7358169, baseEnd_7358169] using wordTrace_append hprefix tailTrace_7358169
  have hstable : (prefixWord ++ tailWord_7358169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358169).length < 2 ^ (prefixWord ++ tailWord_7358169).sum := by decide
  have hdescent : baseEnd_7358169 < baseStart_7358169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358179 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 1, 6]
def baseStart_7358179 : Nat := 118140960795 + 7358179 * 2 ^ 59
def prefixEnd_7358179 : Nat := 4983230072969 + 3 ^ 40 * 7358179 * 2
def baseEnd_7358179 : Nat := 1259427522939823941507619

theorem tailTrace_7358179 : CollatzResearch.WordTrace tailWord_7358179 prefixEnd_7358179 1259427522939823941507619 := by
  unfold tailWord_7358179
  simp only [CollatzResearch.WordTrace]
  refine ⟨268374836009581634769149591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178916557339721089846099727 268374836009581634769149591)
  ·
    refine ⟨402562254014372452153724387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268374836009581634769149591 402562254014372452153724387)
    ·
      refine ⟨603843381021558678230586581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402562254014372452153724387 603843381021558678230586581)
      ·
        refine ⟨14152579242692781521029373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 603843381021558678230586581 14152579242692781521029373)
        ·
          refine ⟨5307217216009793070386015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14152579242692781521029373 5307217216009793070386015)
          ·
            refine ⟨7960825824014689605579023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307217216009793070386015 7960825824014689605579023)
            ·
              refine ⟨11941238736022034408368535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7960825824014689605579023 11941238736022034408368535)
              ·
                refine ⟨17911858104033051612552803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11941238736022034408368535 17911858104033051612552803)
                ·
                  refine ⟨26867787156049577418829205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17911858104033051612552803 26867787156049577418829205)
                  ·
                    refine ⟨1259427522939823941507619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26867787156049577418829205 1259427522939823941507619)
                    ·
                      rfl

theorem cell23_7358179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 1, 6].length) (baseStart_7358179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358179 prefixEnd_7358179 := by exact prefixLift 7358179
  have htrace : WordTrace (prefixWord ++ tailWord_7358179) baseStart_7358179 baseEnd_7358179 := by
    simpa [prefixWord, tailWord_7358179, baseEnd_7358179] using wordTrace_append hprefix tailTrace_7358179
  have hstable : (prefixWord ++ tailWord_7358179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358179).length < 2 ^ (prefixWord ++ tailWord_7358179).sum := by decide
  have hdescent : baseEnd_7358179 < baseStart_7358179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358188 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 2, 7]
def baseStart_7358188 : Nat := 118140960795 + 7358188 * 2 ^ 59
def prefixEnd_7358188 : Nat := 4983230072969 + 3 ^ 40 * 7358188 * 2
def baseEnd_7358188 : Nat := 1259429063381787429770105

theorem tailTrace_7358188 : CollatzResearch.WordTrace tailWord_7358188 prefixEnd_7358188 1259429063381787429770105 := by
  unfold tailWord_7358188
  simp only [CollatzResearch.WordTrace]
  refine ⟨134187582133274514653113609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178916776177699352870818145 134187582133274514653113609)
  ·
    refine ⟨100640686599955885989835207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134187582133274514653113609 100640686599955885989835207)
    ·
      refine ⟨150961029899933828984752811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100640686599955885989835207 150961029899933828984752811)
      ·
        refine ⟨226441544849900743477129217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150961029899933828984752811 226441544849900743477129217)
        ·
          refine ⟨169831158637425557607846913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226441544849900743477129217 169831158637425557607846913)
          ·
            refine ⟨127373368978069168205885185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169831158637425557607846913 127373368978069168205885185)
            ·
              refine ⟨95530026733551876154413889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127373368978069168205885185 95530026733551876154413889)
              ·
                refine ⟨71647520050163907115810417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95530026733551876154413889 71647520050163907115810417)
                ·
                  refine ⟨53735640037622930336857813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71647520050163907115810417 53735640037622930336857813)
                  ·
                    refine ⟨1259429063381787429770105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53735640037622930336857813 1259429063381787429770105)
                    ·
                      rfl

theorem cell23_7358188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_7358188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358188 prefixEnd_7358188 := by exact prefixLift 7358188
  have htrace : WordTrace (prefixWord ++ tailWord_7358188) baseStart_7358188 baseEnd_7358188 := by
    simpa [prefixWord, tailWord_7358188, baseEnd_7358188] using wordTrace_append hprefix tailTrace_7358188
  have hstable : (prefixWord ++ tailWord_7358188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358188).length < 2 ^ (prefixWord ++ tailWord_7358188).sum := by decide
  have hdescent : baseEnd_7358188 < baseStart_7358188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358189 : List Nat := [1, 5, 1, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_7358189 : Nat := 118140960795 + 7358189 * 2 ^ 59
def prefixEnd_7358189 : Nat := 4983230072969 + 3 ^ 40 * 7358189 * 2
def baseEnd_7358189 : Nat := 3778287703626016785397811

theorem tailTrace_7358189 : CollatzResearch.WordTrace tailWord_7358189 prefixEnd_7358189 3778287703626016785397811 := by
  unfold tailWord_7358189
  simp only [CollatzResearch.WordTrace]
  refine ⟨268375200739545406477013621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178916800493030270984675747 268375200739545406477013621)
  ·
    refine ⟨25160175069332381857220027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268375200739545406477013621 25160175069332381857220027)
    ·
      refine ⟨37740262603998572785830041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25160175069332381857220027 37740262603998572785830041)
      ·
        refine ⟨28305196952998929589372531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37740262603998572785830041 28305196952998929589372531)
        ·
          refine ⟨42457795429498394384058797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28305196952998929589372531 42457795429498394384058797)
          ·
            refine ⟨15921673286061897894022049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42457795429498394384058797 15921673286061897894022049)
            ·
              refine ⟨11941254964546423420516537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15921673286061897894022049 11941254964546423420516537)
              ·
                refine ⟨8955941223409817565387403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11941254964546423420516537 8955941223409817565387403)
                ·
                  refine ⟨13433911835114726348081105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8955941223409817565387403 13433911835114726348081105)
                  ·
                    refine ⟨10075433876336044761060829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13433911835114726348081105 10075433876336044761060829)
                    ·
                      refine ⟨3778287703626016785397811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10075433876336044761060829 3778287703626016785397811)
                      ·
                        rfl

theorem cell23_7358189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_7358189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358189 prefixEnd_7358189 := by exact prefixLift 7358189
  have htrace : WordTrace (prefixWord ++ tailWord_7358189) baseStart_7358189 baseEnd_7358189 := by
    simpa [prefixWord, tailWord_7358189, baseEnd_7358189] using wordTrace_append hprefix tailTrace_7358189
  have hstable : (prefixWord ++ tailWord_7358189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358189).length < 2 ^ (prefixWord ++ tailWord_7358189).sum := by decide
  have hdescent : baseEnd_7358189 < baseStart_7358189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358214 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7358214 : Nat := 118140960795 + 7358214 * 2 ^ 59
def prefixEnd_7358214 : Nat := 4983230072969 + 3 ^ 40 * 7358214 * 2
def baseEnd_7358214 : Nat := 3778300540642379187585197

theorem tailTrace_7358214 : CollatzResearch.WordTrace tailWord_7358214 prefixEnd_7358214 3778300540642379187585197 := by
  unfold tailWord_7358214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8386753517639213617083553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178917408376303223831115797 8386753517639213617083553)
  ·
    refine ⟨6290065138229410212812665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8386753517639213617083553 6290065138229410212812665)
    ·
      refine ⟨4717548853672057659609499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6290065138229410212812665 4717548853672057659609499)
      ·
        refine ⟨7076323280508086489414249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4717548853672057659609499 7076323280508086489414249)
        ·
          refine ⟨5307242460381064867060687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7076323280508086489414249 5307242460381064867060687)
          ·
            refine ⟨7960863690571597300591031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307242460381064867060687 7960863690571597300591031)
            ·
              refine ⟨11941295535857395950886547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7960863690571597300591031 11941295535857395950886547)
              ·
                refine ⟨17911943303786093926329821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11941295535857395950886547 17911943303786093926329821)
                ·
                  refine ⟨6716978738919785222373683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17911943303786093926329821 6716978738919785222373683)
                  ·
                    refine ⟨10075468108379677833560525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6716978738919785222373683 10075468108379677833560525)
                    ·
                      refine ⟨3778300540642379187585197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10075468108379677833560525 3778300540642379187585197)
                      ·
                        rfl

theorem cell23_7358214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7358214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358214 prefixEnd_7358214 := by exact prefixLift 7358214
  have htrace : WordTrace (prefixWord ++ tailWord_7358214) baseStart_7358214 baseEnd_7358214 := by
    simpa [prefixWord, tailWord_7358214, baseEnd_7358214] using wordTrace_append hprefix tailTrace_7358214
  have hstable : (prefixWord ++ tailWord_7358214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358214).length < 2 ^ (prefixWord ++ tailWord_7358214).sum := by decide
  have hdescent : baseEnd_7358214 < baseStart_7358214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358245 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_7358245 : Nat := 118140960795 + 7358245 * 2 ^ 59
def prefixEnd_7358245 : Nat := 4983230072969 + 3 ^ 40 * 7358245 * 2
def baseEnd_7358245 : Nat := 3778316458542668566297553

theorem tailTrace_7358245 : CollatzResearch.WordTrace tailWord_7358245 prefixEnd_7358245 3778316458542668566297553 := by
  unfold tailWord_7358245
  simp only [CollatzResearch.WordTrace]
  refine ⟨268377243227342528041052189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178918162151561685360701459 268377243227342528041052189)
  ·
    refine ⟨100641466210253448015394571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268377243227342528041052189 100641466210253448015394571)
    ·
      refine ⟨150962199315380172023091857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100641466210253448015394571 150962199315380172023091857)
      ·
        refine ⟨113221649486535129017318893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150962199315380172023091857 113221649486535129017318893)
        ·
          refine ⟨42458118557450673381494585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113221649486535129017318893 42458118557450673381494585)
          ·
            refine ⟨31843588918088005036120939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42458118557450673381494585 31843588918088005036120939)
            ·
              refine ⟨47765383377132007554181409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31843588918088005036120939 47765383377132007554181409)
              ·
                refine ⟨35824037532849005665636057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47765383377132007554181409 35824037532849005665636057)
                ·
                  refine ⟨26868028149636754249227043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35824037532849005665636057 26868028149636754249227043)
                  ·
                    refine ⟨40302042224455131373840565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26868028149636754249227043 40302042224455131373840565)
                    ·
                      refine ⟨3778316458542668566297553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40302042224455131373840565 3778316458542668566297553)
                      ·
                        rfl

theorem cell23_7358245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_7358245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358245 prefixEnd_7358245 := by exact prefixLift 7358245
  have htrace : WordTrace (prefixWord ++ tailWord_7358245) baseStart_7358245 baseEnd_7358245 := by
    simpa [prefixWord, tailWord_7358245, baseEnd_7358245] using wordTrace_append hprefix tailTrace_7358245
  have hstable : (prefixWord ++ tailWord_7358245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358245).length < 2 ^ (prefixWord ++ tailWord_7358245).sum := by decide
  have hdescent : baseEnd_7358245 < baseStart_7358245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358259 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 1, 4, 2]
def baseStart_7358259 : Nat := 118140960795 + 7358259 * 2 ^ 59
def prefixEnd_7358259 : Nat := 4983230072969 + 3 ^ 40 * 7358259 * 2
def baseEnd_7358259 : Nat := 3778323647271831511522489

theorem tailTrace_7358259 : CollatzResearch.WordTrace tailWord_7358259 prefixEnd_7358259 3778323647271831511522489 := by
  unfold tailWord_7358259
  simp only [CollatzResearch.WordTrace]
  refine ⟨268377753849291808432061831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178918502566194538954707887 268377753849291808432061831)
  ·
    refine ⟨402566630773937712648092747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268377753849291808432061831 402566630773937712648092747)
    ·
      refine ⟨603849946160906568972139121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402566630773937712648092747 603849946160906568972139121)
      ·
        refine ⟨452887459620679926729104341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 603849946160906568972139121 452887459620679926729104341)
        ·
          refine ⟨10614549834859685782713383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 452887459620679926729104341 10614549834859685782713383)
          ·
            refine ⟨15921824752289528674070075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10614549834859685782713383 15921824752289528674070075)
            ·
              refine ⟨23882737128434293011105113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15921824752289528674070075 23882737128434293011105113)
              ·
                refine ⟨17912052846325719758328835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23882737128434293011105113 17912052846325719758328835)
                ·
                  refine ⟨26868079269488579637493253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17912052846325719758328835 26868079269488579637493253)
                  ·
                    refine ⟨5037764863029108682029985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26868079269488579637493253 5037764863029108682029985)
                    ·
                      refine ⟨3778323647271831511522489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5037764863029108682029985 3778323647271831511522489)
                      ·
                        rfl

theorem cell23_7358259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 4, 2].length) (baseStart_7358259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358259 prefixEnd_7358259 := by exact prefixLift 7358259
  have htrace : WordTrace (prefixWord ++ tailWord_7358259) baseStart_7358259 baseEnd_7358259 := by
    simpa [prefixWord, tailWord_7358259, baseEnd_7358259] using wordTrace_append hprefix tailTrace_7358259
  have hstable : (prefixWord ++ tailWord_7358259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358259).length < 2 ^ (prefixWord ++ tailWord_7358259).sum := by decide
  have hdescent : baseEnd_7358259 < baseStart_7358259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358282 : List Nat := [3, 1, 2, 1, 1, 1, 5, 4, 5]
def baseStart_7358282 : Nat := 118140960795 + 7358282 * 2 ^ 59
def prefixEnd_7358282 : Nat := 4983230072969 + 3 ^ 40 * 7358282 * 2
def baseEnd_7358282 : Nat := 419815050814098324614987

theorem tailTrace_7358282 : CollatzResearch.WordTrace tailWord_7358282 prefixEnd_7358282 419815050814098324614987 := by
  unfold tailWord_7358282
  simp only [CollatzResearch.WordTrace]
  refine ⟨67094648182052120840037275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178919061818805655573432733 67094648182052120840037275)
  ·
    refine ⟨100641972273078181260055913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67094648182052120840037275 100641972273078181260055913)
    ·
      refine ⟨75481479204808635945041935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100641972273078181260055913 75481479204808635945041935)
      ·
        refine ⟨113222218807212953917562903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75481479204808635945041935 113222218807212953917562903)
        ·
          refine ⟨169833328210819430876344355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113222218807212953917562903 169833328210819430876344355)
          ·
            refine ⟨254749992316229146314516533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169833328210819430876344355 254749992316229146314516533)
            ·
              refine ⟨23882811779646482466985925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254749992316229146314516533 23882811779646482466985925)
              ·
                refine ⟨4478027208683715462559861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23882811779646482466985925 4478027208683715462559861)
                ·
                  refine ⟨419815050814098324614987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4478027208683715462559861 419815050814098324614987)
                  ·
                    rfl

theorem cell23_7358282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 5].length) (baseStart_7358282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358282 prefixEnd_7358282 := by exact prefixLift 7358282
  have htrace : WordTrace (prefixWord ++ tailWord_7358282) baseStart_7358282 baseEnd_7358282 := by
    simpa [prefixWord, tailWord_7358282, baseEnd_7358282] using wordTrace_append hprefix tailTrace_7358282
  have hstable : (prefixWord ++ tailWord_7358282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358282).length < 2 ^ (prefixWord ++ tailWord_7358282).sum := by decide
  have hdescent : baseEnd_7358282 < baseStart_7358282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358292 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_7358292 : Nat := 118140960795 + 7358292 * 2 ^ 59
def prefixEnd_7358292 : Nat := 4983230072969 + 3 ^ 40 * 7358292 * 2
def baseEnd_7358292 : Nat := 3778340592133429882409837

theorem tailTrace_7358292 : CollatzResearch.WordTrace tailWord_7358292 prefixEnd_7358292 3778340592133429882409837 := by
  unfold tailWord_7358292
  simp only [CollatzResearch.WordTrace]
  refine ⟨134189478729086127534006565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178919304972114836712008753 134189478729086127534006565)
  ·
    refine ⟨25160527261703648912626231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134189478729086127534006565 25160527261703648912626231)
    ·
      refine ⟨37740790892555473368939347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25160527261703648912626231 37740790892555473368939347)
      ·
        refine ⟨56611186338833210053409021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37740790892555473368939347 56611186338833210053409021)
        ·
          refine ⟨21229194877062453770028383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56611186338833210053409021 21229194877062453770028383)
          ·
            refine ⟨31843792315593680655042575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21229194877062453770028383 31843792315593680655042575)
            ·
              refine ⟨47765688473390520982563863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31843792315593680655042575 47765688473390520982563863)
              ·
                refine ⟨71648532710085781473845795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47765688473390520982563863 71648532710085781473845795)
                ·
                  refine ⟨107472799065128672210768693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71648532710085781473845795 107472799065128672210768693)
                  ·
                    refine ⟨10075574912355813019759565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107472799065128672210768693 10075574912355813019759565)
                    ·
                      refine ⟨3778340592133429882409837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10075574912355813019759565 3778340592133429882409837)
                      ·
                        rfl

theorem cell23_7358292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_7358292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358292 prefixEnd_7358292 := by exact prefixLift 7358292
  have htrace : WordTrace (prefixWord ++ tailWord_7358292) baseStart_7358292 baseEnd_7358292 := by
    simpa [prefixWord, tailWord_7358292, baseEnd_7358292] using wordTrace_append hprefix tailTrace_7358292
  have hstable : (prefixWord ++ tailWord_7358292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358292).length < 2 ^ (prefixWord ++ tailWord_7358292).sum := by decide
  have hdescent : baseEnd_7358292 < baseStart_7358292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358345 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 6]
def baseStart_7358345 : Nat := 118140960795 + 7358345 * 2 ^ 59
def prefixEnd_7358345 : Nat := 4983230072969 + 3 ^ 40 * 7358345 * 2
def baseEnd_7358345 : Nat := 3778367806608118175047093

theorem tailTrace_7358345 : CollatzResearch.WordTrace tailWord_7358345 prefixEnd_7358345 3778367806608118175047093 := by
  unfold tailWord_7358345
  simp only [CollatzResearch.WordTrace]
  refine ⟨268380890526980245119692489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178920593684653496746461659 268380890526980245119692489)
  ·
    refine ⟨201285667895235183839769367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268380890526980245119692489 201285667895235183839769367)
    ·
      refine ⟨301928501842852775759654051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201285667895235183839769367 301928501842852775759654051)
      ·
        refine ⟨452892752764279163639481077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301928501842852775759654051 452892752764279163639481077)
        ·
          refine ⟨42458695571651171591201351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 452892752764279163639481077 42458695571651171591201351)
          ·
            refine ⟨63688043357476757386802027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42458695571651171591201351 63688043357476757386802027)
            ·
              refine ⟨95532065036215136080203041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63688043357476757386802027 95532065036215136080203041)
              ·
                refine ⟨71649048777161352060152281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95532065036215136080203041 71649048777161352060152281)
                ·
                  refine ⟨53736786582871014045114211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71649048777161352060152281 53736786582871014045114211)
                  ·
                    refine ⟨80605179874306521067671317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53736786582871014045114211 80605179874306521067671317)
                    ·
                      refine ⟨3778367806608118175047093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80605179874306521067671317 3778367806608118175047093)
                      ·
                        rfl

theorem cell23_7358345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_7358345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358345 prefixEnd_7358345 := by exact prefixLift 7358345
  have htrace : WordTrace (prefixWord ++ tailWord_7358345) baseStart_7358345 baseEnd_7358345 := by
    simpa [prefixWord, tailWord_7358345, baseEnd_7358345] using wordTrace_append hprefix tailTrace_7358345
  have hstable : (prefixWord ++ tailWord_7358345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358345).length < 2 ^ (prefixWord ++ tailWord_7358345).sum := by decide
  have hdescent : baseEnd_7358345 < baseStart_7358345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358432 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 6, 4]
def baseStart_7358432 : Nat := 118140960795 + 7358432 * 2 ^ 59
def prefixEnd_7358432 : Nat := 4983230072969 + 3 ^ 40 * 7358432 * 2
def baseEnd_7358432 : Nat := 1259470826475019778219731

theorem tailTrace_7358432 : CollatzResearch.WordTrace tailWord_7358432 prefixEnd_7358432 1259470826475019778219731 := by
  unfold tailWord_7358432
  simp only [CollatzResearch.WordTrace]
  refine ⟨134192031838832529489054775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178922709118443372652073033 134192031838832529489054775)
  ·
    refine ⟨201288047758248794233582163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134192031838832529489054775 201288047758248794233582163)
    ·
      refine ⟨301932071637373191350373245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201288047758248794233582163 301932071637373191350373245)
      ·
        refine ⟨113224526864014946756389967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301932071637373191350373245 113224526864014946756389967)
        ·
          refine ⟨169836790296022420134584951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113224526864014946756389967 169836790296022420134584951)
          ·
            refine ⟨254755185444033630201877427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169836790296022420134584951 254755185444033630201877427)
            ·
              refine ⟨382132778166050445302816141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254755185444033630201877427 382132778166050445302816141)
              ·
                refine ⟨143299791812268916988556053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382132778166050445302816141 143299791812268916988556053)
                ·
                  refine ⟨6717177741200105483838565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143299791812268916988556053 6717177741200105483838565)
                  ·
                    refine ⟨1259470826475019778219731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6717177741200105483838565 1259470826475019778219731)
                    ·
                      rfl

theorem cell23_7358432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 6, 4].length) (baseStart_7358432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358432 prefixEnd_7358432 := by exact prefixLift 7358432
  have htrace : WordTrace (prefixWord ++ tailWord_7358432) baseStart_7358432 baseEnd_7358432 := by
    simpa [prefixWord, tailWord_7358432, baseEnd_7358432] using wordTrace_append hprefix tailTrace_7358432
  have hstable : (prefixWord ++ tailWord_7358432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358432).length < 2 ^ (prefixWord ++ tailWord_7358432).sum := by decide
  have hdescent : baseEnd_7358432 < baseStart_7358432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358469 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 1, 2, 4]
def baseStart_7358469 : Nat := 118140960795 + 7358469 * 2 ^ 59
def prefixEnd_7358469 : Nat := 4983230072969 + 3 ^ 40 * 7358469 * 2
def baseEnd_7358469 : Nat := 3778431478209275689896523

theorem tailTrace_7358469 : CollatzResearch.WordTrace tailWord_7358469 prefixEnd_7358469 3778431478209275689896523 := by
  unfold tailWord_7358469
  simp only [CollatzResearch.WordTrace]
  refine ⟨268385413178531014297206461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178923608785687342864804307 268385413178531014297206461)
  ·
    refine ⟨100644529941949130361452423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268385413178531014297206461 100644529941949130361452423)
    ·
      refine ⟨150966794912923695542178635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100644529941949130361452423 150966794912923695542178635)
      ·
        refine ⟨226450192369385543313267953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150966794912923695542178635 226450192369385543313267953)
        ·
          refine ⟨169837644277039157484950965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226450192369385543313267953 169837644277039157484950965)
          ·
            refine ⟨15922279150972421014214153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169837644277039157484950965 15922279150972421014214153)
            ·
              refine ⟨11941709363229315760660615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15922279150972421014214153 11941709363229315760660615)
              ·
                refine ⟨17912564044843973640990923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11941709363229315760660615 17912564044843973640990923)
                ·
                  refine ⟨26868846067265960461486385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17912564044843973640990923 26868846067265960461486385)
                  ·
                    refine ⟨20151634550449470346114789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26868846067265960461486385 20151634550449470346114789)
                    ·
                      refine ⟨3778431478209275689896523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20151634550449470346114789 3778431478209275689896523)
                      ·
                        rfl

theorem cell23_7358469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_7358469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358469 prefixEnd_7358469 := by exact prefixLift 7358469
  have htrace : WordTrace (prefixWord ++ tailWord_7358469) baseStart_7358469 baseEnd_7358469 := by
    simpa [prefixWord, tailWord_7358469, baseEnd_7358469] using wordTrace_append hprefix tailTrace_7358469
  have hstable : (prefixWord ++ tailWord_7358469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358469).length < 2 ^ (prefixWord ++ tailWord_7358469).sum := by decide
  have hdescent : baseEnd_7358469 < baseStart_7358469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358489 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 4, 1, 3]
def baseStart_7358489 : Nat := 118140960795 + 7358489 * 2 ^ 59
def prefixEnd_7358489 : Nat := 4983230072969 + 3 ^ 40 * 7358489 * 2
def baseEnd_7358489 : Nat := 3778441747822365611646431

theorem tailTrace_7358489 : CollatzResearch.WordTrace tailWord_7358489 prefixEnd_7358489 3778441747822365611646431 := by
  unfold tailWord_7358489
  simp only [CollatzResearch.WordTrace]
  refine ⟨268386142638458557712934521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178924095092305705141956347 268386142638458557712934521)
  ·
    refine ⟨201289606978843918284700891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268386142638458557712934521 201289606978843918284700891)
    ·
      refine ⟨301934410468265877427051337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201289606978843918284700891 301934410468265877427051337)
      ·
        refine ⟨226450807851199408070288503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301934410468265877427051337 226450807851199408070288503)
        ·
          refine ⟨339676211776799112105432755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226450807851199408070288503 339676211776799112105432755)
          ·
            refine ⟨509514317665198668158149133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339676211776799112105432755 509514317665198668158149133)
            ·
              refine ⟨191067869124449500559305925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 509514317665198668158149133 191067869124449500559305925)
              ·
                refine ⟨35825225460834281354869861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191067869124449500559305925 35825225460834281354869861)
                ·
                  refine ⟨6717229773906427754038099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35825225460834281354869861 6717229773906427754038099)
                  ·
                    refine ⟨10075844660859641631057149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6717229773906427754038099 10075844660859641631057149)
                    ·
                      refine ⟨3778441747822365611646431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10075844660859641631057149 3778441747822365611646431)
                      ·
                        rfl

theorem cell23_7358489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_7358489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358489 prefixEnd_7358489 := by exact prefixLift 7358489
  have htrace : WordTrace (prefixWord ++ tailWord_7358489) baseStart_7358489 baseEnd_7358489 := by
    simpa [prefixWord, tailWord_7358489, baseEnd_7358489] using wordTrace_append hprefix tailTrace_7358489
  have hstable : (prefixWord ++ tailWord_7358489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358489).length < 2 ^ (prefixWord ++ tailWord_7358489).sum := by decide
  have hdescent : baseEnd_7358489 < baseStart_7358489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358490 : List Nat := [3, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2]
def baseStart_7358490 : Nat := 118140960795 + 7358490 * 2 ^ 59
def prefixEnd_7358490 : Nat := 4983230072969 + 3 ^ 40 * 7358490 * 2
def baseEnd_7358490 : Nat := 3778442261303020107733927

theorem tailTrace_7358490 : CollatzResearch.WordTrace tailWord_7358490 prefixEnd_7358490 3778442261303020107733927 := by
  unfold tailWord_7358490
  simp only [CollatzResearch.WordTrace]
  refine ⟨67096544777863733720930231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178924119407636623255813949 67096544777863733720930231)
  ·
    refine ⟨100644817166795600581395347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67096544777863733720930231 100644817166795600581395347)
    ·
      refine ⟨150967225750193400872093021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100644817166795600581395347 150967225750193400872093021)
      ·
        refine ⟨56612709656322525327034883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150967225750193400872093021 56612709656322525327034883)
        ·
          refine ⟨84919064484483787990552325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56612709656322525327034883 84919064484483787990552325)
          ·
            refine ⟨15922324590840710248228561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84919064484483787990552325 15922324590840710248228561)
            ·
              refine ⟨11941743443130532686171421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15922324590840710248228561 11941743443130532686171421)
              ·
                refine ⟨4478153791173949757314283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11941743443130532686171421 4478153791173949757314283)
                ·
                  refine ⟨6717230686760924635971425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4478153791173949757314283 6717230686760924635971425)
                  ·
                    refine ⟨5037923015070693476978569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6717230686760924635971425 5037923015070693476978569)
                    ·
                      refine ⟨3778442261303020107733927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5037923015070693476978569 3778442261303020107733927)
                      ·
                        rfl

theorem cell23_7358490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_7358490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358490 prefixEnd_7358490 := by exact prefixLift 7358490
  have htrace : WordTrace (prefixWord ++ tailWord_7358490) baseStart_7358490 baseEnd_7358490 := by
    simpa [prefixWord, tailWord_7358490, baseEnd_7358490] using wordTrace_append hprefix tailTrace_7358490
  have hstable : (prefixWord ++ tailWord_7358490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358490).length < 2 ^ (prefixWord ++ tailWord_7358490).sum := by decide
  have hdescent : baseEnd_7358490 < baseStart_7358490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358493 : List Nat := [1, 4, 2, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_7358493 : Nat := 118140960795 + 7358493 * 2 ^ 59
def prefixEnd_7358493 : Nat := 4983230072969 + 3 ^ 40 * 7358493 * 2
def baseEnd_7358493 : Nat := 3778443801744983595996413

theorem tailTrace_7358493 : CollatzResearch.WordTrace tailWord_7358493 prefixEnd_7358493 3778443801744983595996413 := by
  unfold tailWord_7358493
  simp only [CollatzResearch.WordTrace]
  refine ⟨268386288530444066396080133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178924192353629377597386755 268386288530444066396080133)
  ·
    refine ⟨50322429099458262449265025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268386288530444066396080133 50322429099458262449265025)
    ·
      refine ⟨37741821824593696836948769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50322429099458262449265025 37741821824593696836948769)
      ·
        refine ⟨28306366368445272627711577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37741821824593696836948769 28306366368445272627711577)
        ·
          refine ⟨21229774776333954470783683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28306366368445272627711577 21229774776333954470783683)
          ·
            refine ⟨31844662164500931706175525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21229774776333954470783683 31844662164500931706175525)
            ·
              refine ⟨5970874155843924694907911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31844662164500931706175525 5970874155843924694907911)
              ·
                refine ⟨8956311233765887042361867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5970874155843924694907911 8956311233765887042361867)
                ·
                  refine ⟨13434466850648830563542801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8956311233765887042361867 13434466850648830563542801)
                  ·
                    refine ⟨10075850137986622922657101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13434466850648830563542801 10075850137986622922657101)
                    ·
                      refine ⟨3778443801744983595996413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10075850137986622922657101 3778443801744983595996413)
                      ·
                        rfl

theorem cell23_7358493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_7358493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358493 prefixEnd_7358493 := by exact prefixLift 7358493
  have htrace : WordTrace (prefixWord ++ tailWord_7358493) baseStart_7358493 baseEnd_7358493 := by
    simpa [prefixWord, tailWord_7358493, baseEnd_7358493] using wordTrace_append hprefix tailTrace_7358493
  have hstable : (prefixWord ++ tailWord_7358493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358493).length < 2 ^ (prefixWord ++ tailWord_7358493).sum := by decide
  have hdescent : baseEnd_7358493 < baseStart_7358493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358500 : List Nat := [2, 3, 1, 4, 3, 1, 1, 2, 2, 4]
def baseStart_7358500 : Nat := 118140960795 + 7358500 * 2 ^ 59
def prefixEnd_7358500 : Nat := 4983230072969 + 3 ^ 40 * 7358500 * 2
def baseEnd_7358500 : Nat := 1259482465369855022869627

theorem tailTrace_7358500 : CollatzResearch.WordTrace tailWord_7358500 prefixEnd_7358500 1259482465369855022869627 := by
  unfold tailWord_7358500
  simp only [CollatzResearch.WordTrace]
  refine ⟨134193271920709353295792477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178924362560945804394389969 134193271920709353295792477)
  ·
    refine ⟨50322476970266007485922179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134193271920709353295792477 50322476970266007485922179)
    ·
      refine ⟨75483715455399011228883269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50322476970266007485922179 75483715455399011228883269)
      ·
        refine ⟨14153196647887314605415613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75483715455399011228883269 14153196647887314605415613)
        ·
          refine ⟨5307448742957742977030855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14153196647887314605415613 5307448742957742977030855)
          ·
            refine ⟨7961173114436614465546283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307448742957742977030855 7961173114436614465546283)
            ·
              refine ⟨11941759671654921698319425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7961173114436614465546283 11941759671654921698319425)
              ·
                refine ⟨8956319753741191273739569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11941759671654921698319425 8956319753741191273739569)
                ·
                  refine ⟨6717239815305893455304677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8956319753741191273739569 6717239815305893455304677)
                  ·
                    refine ⟨1259482465369855022869627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6717239815305893455304677 1259482465369855022869627)
                    ·
                      rfl

theorem cell23_7358500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_7358500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358500 prefixEnd_7358500 := by exact prefixLift 7358500
  have htrace : WordTrace (prefixWord ++ tailWord_7358500) baseStart_7358500 baseEnd_7358500 := by
    simpa [prefixWord, tailWord_7358500, baseEnd_7358500] using wordTrace_append hprefix tailTrace_7358500
  have hstable : (prefixWord ++ tailWord_7358500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358500).length < 2 ^ (prefixWord ++ tailWord_7358500).sum := by decide
  have hdescent : baseEnd_7358500 < baseStart_7358500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358549 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_7358549 : Nat := 118140960795 + 7358549 * 2 ^ 59
def prefixEnd_7358549 : Nat := 4983230072969 + 3 ^ 40 * 7358549 * 2
def baseEnd_7358549 : Nat := 3778472556661635376896155

theorem tailTrace_7358549 : CollatzResearch.WordTrace tailWord_7358549 prefixEnd_7358549 3778472556661635376896155 := by
  unfold tailWord_7358549
  simp only [CollatzResearch.WordTrace]
  refine ⟨268388331018241187960118701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178925554012160791973412467 268388331018241187960118701)
  ·
    refine ⟨100645624131840445485044513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268388331018241187960118701 100645624131840445485044513)
    ·
      refine ⟨75484218098880334113783385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100645624131840445485044513 75484218098880334113783385)
      ·
        refine ⟨56613163574160250585337539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75484218098880334113783385 56613163574160250585337539)
        ·
          refine ⟨84919745361240375878006309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56613163574160250585337539 84919745361240375878006309)
          ·
            refine ⟨15922452255232570477126183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84919745361240375878006309 15922452255232570477126183)
            ·
              refine ⟨23883678382848855715689275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15922452255232570477126183 23883678382848855715689275)
              ·
                refine ⟨35825517574273283573533913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23883678382848855715689275 35825517574273283573533913)
                ·
                  refine ⟨26869138180704962680150435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35825517574273283573533913 26869138180704962680150435)
                  ·
                    refine ⟨40303707271057444020225653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26869138180704962680150435 40303707271057444020225653)
                    ·
                      refine ⟨3778472556661635376896155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40303707271057444020225653 3778472556661635376896155)
                      ·
                        rfl

theorem cell23_7358549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_7358549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358549 prefixEnd_7358549 := by exact prefixLift 7358549
  have htrace : WordTrace (prefixWord ++ tailWord_7358549) baseStart_7358549 baseEnd_7358549 := by
    simpa [prefixWord, tailWord_7358549, baseEnd_7358549] using wordTrace_append hprefix tailTrace_7358549
  have hstable : (prefixWord ++ tailWord_7358549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358549).length < 2 ^ (prefixWord ++ tailWord_7358549).sum := by decide
  have hdescent : baseEnd_7358549 < baseStart_7358549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358592 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 7]
def baseStart_7358592 : Nat := 118140960795 + 7358592 * 2 ^ 59
def prefixEnd_7358592 : Nat := 4983230072969 + 3 ^ 40 * 7358592 * 2
def baseEnd_7358592 : Nat := 3778494636329778708658457

theorem tailTrace_7358592 : CollatzResearch.WordTrace tailWord_7358592 prefixEnd_7358592 3778494636329778708658457 := by
  unfold tailWord_7358592
  simp only [CollatzResearch.WordTrace]
  refine ⟨134194949678542703151967015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178926599571390270869289353 134194949678542703151967015)
  ·
    refine ⟨201292424517814054727950523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134194949678542703151967015 201292424517814054727950523)
    ·
      refine ⟨301938636776721082091925785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201292424517814054727950523 301938636776721082091925785)
      ·
        refine ⟨226453977582540811568944339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301938636776721082091925785 226453977582540811568944339)
        ·
          refine ⟨339680966373811217353416509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226453977582540811568944339 339680966373811217353416509)
          ·
            refine ⟨127380362390179206507531191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339680966373811217353416509 127380362390179206507531191)
            ·
              refine ⟨191070543585268809761296787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127380362390179206507531191 191070543585268809761296787)
              ·
                refine ⟨286605815377903214641945181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191070543585268809761296787 286605815377903214641945181)
                ·
                  refine ⟨107477180766713705490729443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286605815377903214641945181 107477180766713705490729443)
                  ·
                    refine ⟨161215771150070558236094165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107477180766713705490729443 161215771150070558236094165)
                    ·
                      refine ⟨3778494636329778708658457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161215771150070558236094165 3778494636329778708658457)
                      ·
                        rfl

theorem cell23_7358592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_7358592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358592 prefixEnd_7358592 := by exact prefixLift 7358592
  have htrace : WordTrace (prefixWord ++ tailWord_7358592) baseStart_7358592 baseEnd_7358592 := by
    simpa [prefixWord, tailWord_7358592, baseEnd_7358592] using wordTrace_append hprefix tailTrace_7358592
  have hstable : (prefixWord ++ tailWord_7358592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358592).length < 2 ^ (prefixWord ++ tailWord_7358592).sum := by decide
  have hdescent : baseEnd_7358592 < baseStart_7358592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358599 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 2, 5]
def baseStart_7358599 : Nat := 118140960795 + 7358599 * 2 ^ 59
def prefixEnd_7358599 : Nat := 4983230072969 + 3 ^ 40 * 7358599 * 2
def baseEnd_7358599 : Nat := 1259499410231453393756975

theorem tailTrace_7358599 : CollatzResearch.WordTrace tailWord_7358599 prefixEnd_7358599 1259499410231453393756975 := by
  unfold tailWord_7358599
  simp only [CollatzResearch.WordTrace]
  refine ⟨268390154668060046499438851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178926769778706697666292567 268390154668060046499438851)
  ·
    refine ⟨402585232002090069749158277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268390154668060046499438851 402585232002090069749158277)
    ·
      refine ⟨75484731000391888077967177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 402585232002090069749158277 75484731000391888077967177)
      ·
        refine ⟨56613548250293916058475383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75484731000391888077967177 56613548250293916058475383)
        ·
          refine ⟨84920322375440874087713075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56613548250293916058475383 84920322375440874087713075)
          ·
            refine ⟨127380483563161311131569613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84920322375440874087713075 127380483563161311131569613)
            ·
              refine ⟨47767681336185491674338605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127380483563161311131569613 47767681336185491674338605)
              ·
                refine ⟨17912880501069559377876977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47767681336185491674338605 17912880501069559377876977)
                ·
                  refine ⟨13434660375802169533407733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17912880501069559377876977 13434660375802169533407733)
                  ·
                    refine ⟨1259499410231453393756975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13434660375802169533407733 1259499410231453393756975)
                    ·
                      rfl

theorem cell23_7358599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_7358599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358599 prefixEnd_7358599 := by exact prefixLift 7358599
  have htrace : WordTrace (prefixWord ++ tailWord_7358599) baseStart_7358599 baseEnd_7358599 := by
    simpa [prefixWord, tailWord_7358599, baseEnd_7358599] using wordTrace_append hprefix tailTrace_7358599
  have hstable : (prefixWord ++ tailWord_7358599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358599).length < 2 ^ (prefixWord ++ tailWord_7358599).sum := by decide
  have hdescent : baseEnd_7358599 < baseStart_7358599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358619 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 4]
def baseStart_7358619 : Nat := 118140960795 + 7358619 * 2 ^ 59
def prefixEnd_7358619 : Nat := 4983230072969 + 3 ^ 40 * 7358619 * 2
def baseEnd_7358619 : Nat := 3778508500307450103020833

theorem tailTrace_7358619 : CollatzResearch.WordTrace tailWord_7358619 prefixEnd_7358619 3778508500307450103020833 := by
  unfold tailWord_7358619
  simp only [CollatzResearch.WordTrace]
  refine ⟨268390884127987589915166911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178927256085325059943444607 268390884127987589915166911)
  ·
    refine ⟨402586326191981384872750367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268390884127987589915166911 402586326191981384872750367)
    ·
      refine ⟨603879489287972077309125551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402586326191981384872750367 603879489287972077309125551)
      ·
        refine ⟨905819233931958115963688327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603879489287972077309125551 905819233931958115963688327)
        ·
          refine ⟨1358728850897937173945532491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905819233931958115963688327 1358728850897937173945532491)
          ·
            refine ⟨2038093276346905760918298737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1358728850897937173945532491 2038093276346905760918298737)
            ·
              refine ⟨1528569957260179320688724053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2038093276346905760918298737 1528569957260179320688724053)
              ·
                refine ⟨17912929186642726414320985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1528569957260179320688724053 17912929186642726414320985)
                ·
                  refine ⟨13434696889982044810740739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17912929186642726414320985 13434696889982044810740739)
                  ·
                    refine ⟨20152045334973067216111109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13434696889982044810740739 20152045334973067216111109)
                    ·
                      refine ⟨3778508500307450103020833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20152045334973067216111109 3778508500307450103020833)
                      ·
                        rfl

theorem cell23_7358619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 4].length) (baseStart_7358619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358619 prefixEnd_7358619 := by exact prefixLift 7358619
  have htrace : WordTrace (prefixWord ++ tailWord_7358619) baseStart_7358619 baseEnd_7358619 := by
    simpa [prefixWord, tailWord_7358619, baseEnd_7358619] using wordTrace_append hprefix tailTrace_7358619
  have hstable : (prefixWord ++ tailWord_7358619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358619).length < 2 ^ (prefixWord ++ tailWord_7358619).sum := by decide
  have hdescent : baseEnd_7358619 < baseStart_7358619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358626 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_7358626 : Nat := 118140960795 + 7358626 * 2 ^ 59
def prefixEnd_7358626 : Nat := 4983230072969 + 3 ^ 40 * 7358626 * 2
def baseEnd_7358626 : Nat := 3778512094672031575633301

theorem tailTrace_7358626 : CollatzResearch.WordTrace tailWord_7358626 prefixEnd_7358626 3778512094672031575633301 := by
  unfold tailWord_7358626
  simp only [CollatzResearch.WordTrace]
  refine ⟨67097784859740557527667933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178927426292641486740447821 67097784859740557527667933)
  ·
    refine ⟨25161669322402709072875475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67097784859740557527667933 25161669322402709072875475)
    ·
      refine ⟨37742503983604063609313213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25161669322402709072875475 37742503983604063609313213)
      ·
        refine ⟨14153438993851523853492455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37742503983604063609313213 14153438993851523853492455)
        ·
          refine ⟨21230158490777285780238683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14153438993851523853492455 21230158490777285780238683)
          ·
            refine ⟨31845237736165928670358025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21230158490777285780238683 31845237736165928670358025)
            ·
              refine ⟨23883928302124446502768519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31845237736165928670358025 23883928302124446502768519)
              ·
                refine ⟨35825892453186669754152779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23883928302124446502768519 35825892453186669754152779)
                ·
                  refine ⟨53738838679780004631229169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35825892453186669754152779 53738838679780004631229169)
                  ·
                    refine ⟨40304129009835003473421877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53738838679780004631229169 40304129009835003473421877)
                    ·
                      refine ⟨3778512094672031575633301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40304129009835003473421877 3778512094672031575633301)
                      ·
                        rfl

theorem cell23_7358626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_7358626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358626 prefixEnd_7358626 := by exact prefixLift 7358626
  have htrace : WordTrace (prefixWord ++ tailWord_7358626) baseStart_7358626 baseEnd_7358626 := by
    simpa [prefixWord, tailWord_7358626, baseEnd_7358626] using wordTrace_append hprefix tailTrace_7358626
  have hstable : (prefixWord ++ tailWord_7358626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358626).length < 2 ^ (prefixWord ++ tailWord_7358626).sum := by decide
  have hdescent : baseEnd_7358626 < baseStart_7358626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358639 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 3]
def baseStart_7358639 : Nat := 118140960795 + 7358639 * 2 ^ 59
def prefixEnd_7358639 : Nat := 4983230072969 + 3 ^ 40 * 7358639 * 2
def baseEnd_7358639 : Nat := 3778518769920540024770741

theorem tailTrace_7358639 : CollatzResearch.WordTrace tailWord_7358639 prefixEnd_7358639 3778518769920540024770741 := by
  unfold tailWord_7358639
  simp only [CollatzResearch.WordTrace]
  refine ⟨268391613587915133330894971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178927742391943422220596647 268391613587915133330894971)
  ·
    refine ⟨402587420381872699996342457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268391613587915133330894971 402587420381872699996342457)
    ·
      refine ⟨301940565286404524997256843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402587420381872699996342457 301940565286404524997256843)
      ·
        refine ⟨452910847929606787495885265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301940565286404524997256843 452910847929606787495885265)
        ·
          refine ⟨339683135947205090621913949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452910847929606787495885265 339683135947205090621913949)
          ·
            refine ⟨127381175980201908983217731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339683135947205090621913949 127381175980201908983217731)
            ·
              refine ⟨191071763970302863474826597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127381175980201908983217731 191071763970302863474826597)
              ·
                refine ⟨35825955744431786901529987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191071763970302863474826597 35825955744431786901529987)
                ·
                  refine ⟨53738933616647680352294981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35825955744431786901529987 53738933616647680352294981)
                  ·
                    refine ⟨10076050053121440066055309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53738933616647680352294981 10076050053121440066055309)
                    ·
                      refine ⟨3778518769920540024770741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10076050053121440066055309 3778518769920540024770741)
                      ·
                        rfl

theorem cell23_7358639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 3].length) (baseStart_7358639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358639 prefixEnd_7358639 := by exact prefixLift 7358639
  have htrace : WordTrace (prefixWord ++ tailWord_7358639) baseStart_7358639 baseEnd_7358639 := by
    simpa [prefixWord, tailWord_7358639, baseEnd_7358639] using wordTrace_append hprefix tailTrace_7358639
  have hstable : (prefixWord ++ tailWord_7358639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358639).length < 2 ^ (prefixWord ++ tailWord_7358639).sum := by decide
  have hdescent : baseEnd_7358639 < baseStart_7358639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358656 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 3]
def baseStart_7358656 : Nat := 118140960795 + 7358656 * 2 ^ 59
def prefixEnd_7358656 : Nat := 4983230072969 + 3 ^ 40 * 7358656 * 2
def baseEnd_7358656 : Nat := 3778527499091666458258163

theorem tailTrace_7358656 : CollatzResearch.WordTrace tailWord_7358656 prefixEnd_7358656 3778527499091666458258163 := by
  unfold tailWord_7358656
  simp only [CollatzResearch.WordTrace]
  refine ⟨134196116814426772617131911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178928155752569030156175881 134196116814426772617131911)
  ·
    refine ⟨201294175221640158925697867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134196116814426772617131911 201294175221640158925697867)
    ·
      refine ⟨301941262832460238388546801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201294175221640158925697867 301941262832460238388546801)
      ·
        refine ⟨226455947124345178791410101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301941262832460238388546801 226455947124345178791410101)
        ·
          refine ⟨21230245042907360511694697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226455947124345178791410101 21230245042907360511694697)
          ·
            refine ⟨15922683782180520383771023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21230245042907360511694697 15922683782180520383771023)
            ·
              refine ⟨23884025673270780575656535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15922683782180520383771023 23884025673270780575656535)
              ·
                refine ⟨35826038509906170863484803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23884025673270780575656535 35826038509906170863484803)
                ·
                  refine ⟨53739057764859256295227205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35826038509906170863484803 53739057764859256295227205)
                  ·
                    refine ⟨10076073330911110555355101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53739057764859256295227205 10076073330911110555355101)
                    ·
                      refine ⟨3778527499091666458258163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10076073330911110555355101 3778527499091666458258163)
                      ·
                        rfl

theorem cell23_7358656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_7358656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358656 prefixEnd_7358656 := by exact prefixLift 7358656
  have htrace : WordTrace (prefixWord ++ tailWord_7358656) baseStart_7358656 baseEnd_7358656 := by
    simpa [prefixWord, tailWord_7358656, baseEnd_7358656] using wordTrace_append hprefix tailTrace_7358656
  have hstable : (prefixWord ++ tailWord_7358656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358656).length < 2 ^ (prefixWord ++ tailWord_7358656).sum := by decide
  have hdescent : baseEnd_7358656 < baseStart_7358656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358693 : List Nat := [1, 3, 1, 4, 2, 2, 3, 1, 6]
def baseStart_7358693 : Nat := 118140960795 + 7358693 * 2 ^ 59
def prefixEnd_7358693 : Nat := 4983230072969 + 3 ^ 40 * 7358693 * 2
def baseEnd_7358693 : Nat := 419838499763986979277277

theorem tailTrace_7358693 : CollatzResearch.WordTrace tailWord_7358693 prefixEnd_7358693 419838499763986979277277 := by
  unfold tailWord_7358693
  simp only [CollatzResearch.WordTrace]
  refine ⟨268393583129719500553360733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178929055419813000368907155 268393583129719500553360733)
  ·
    refine ⟨100647593673644812707510275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268393583129719500553360733 100647593673644812707510275)
    ·
      refine ⟨150971390510467219061265413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100647593673644812707510275 150971390510467219061265413)
      ·
        refine ⟨28307135720712603573987265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150971390510467219061265413 28307135720712603573987265)
        ·
          refine ⟨21230351790534452680490449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28307135720712603573987265 21230351790534452680490449)
          ·
            refine ⟨15922763842900839510367837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21230351790534452680490449 15922763842900839510367837)
            ·
              refine ⟨5971036441087814816387939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15922763842900839510367837 5971036441087814816387939)
              ·
                refine ⟨8956554661631722224581909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5971036441087814816387939 8956554661631722224581909)
                ·
                  refine ⟨419838499763986979277277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8956554661631722224581909 419838499763986979277277)
                  ·
                    rfl

theorem cell23_7358693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 6].length) (baseStart_7358693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358693 prefixEnd_7358693 := by exact prefixLift 7358693
  have htrace : WordTrace (prefixWord ++ tailWord_7358693) baseStart_7358693 baseEnd_7358693 := by
    simpa [prefixWord, tailWord_7358693, baseEnd_7358693] using wordTrace_append hprefix tailTrace_7358693
  have hstable : (prefixWord ++ tailWord_7358693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358693).length < 2 ^ (prefixWord ++ tailWord_7358693).sum := by decide
  have hdescent : baseEnd_7358693 < baseStart_7358693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358703 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 3, 1, 3]
def baseStart_7358703 : Nat := 118140960795 + 7358703 * 2 ^ 59
def prefixEnd_7358703 : Nat := 4983230072969 + 3 ^ 40 * 7358703 * 2
def baseEnd_7358703 : Nat := 3778551632682427774370447

theorem tailTrace_7358703 : CollatzResearch.WordTrace tailWord_7358703 prefixEnd_7358703 3778551632682427774370447 := by
  unfold tailWord_7358703
  simp only [CollatzResearch.WordTrace]
  refine ⟨268393947859683272261224763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178929298573122181507483175 268393947859683272261224763)
  ·
    refine ⟨402590921789524908391837145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268393947859683272261224763 402590921789524908391837145)
    ·
      refine ⟨301943191342143681293877859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402590921789524908391837145 301943191342143681293877859)
      ·
        refine ⟨452914787013215521940816789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301943191342143681293877859 452914787013215521940816789)
        ·
          refine ⟨21230380641244477590975787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 452914787013215521940816789 21230380641244477590975787)
          ·
            refine ⟨31845570961866716386463681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21230380641244477590975787 31845570961866716386463681)
            ·
              refine ⟨23884178221400037289847761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31845570961866716386463681 23884178221400037289847761)
              ·
                refine ⟨17913133666050027967385821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23884178221400037289847761 17913133666050027967385821)
                ·
                  refine ⟨6717425124768760487769683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17913133666050027967385821 6717425124768760487769683)
                  ·
                    refine ⟨10076137687153140731654525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6717425124768760487769683 10076137687153140731654525)
                    ·
                      refine ⟨3778551632682427774370447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10076137687153140731654525 3778551632682427774370447)
                      ·
                        rfl

theorem cell23_7358703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 1, 3].length) (baseStart_7358703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358703 prefixEnd_7358703 := by exact prefixLift 7358703
  have htrace : WordTrace (prefixWord ++ tailWord_7358703) baseStart_7358703 baseEnd_7358703 := by
    simpa [prefixWord, tailWord_7358703, baseEnd_7358703] using wordTrace_append hprefix tailTrace_7358703
  have hstable : (prefixWord ++ tailWord_7358703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358703).length < 2 ^ (prefixWord ++ tailWord_7358703).sum := by decide
  have hdescent : baseEnd_7358703 < baseStart_7358703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358719 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 3, 6]
def baseStart_7358719 : Nat := 118140960795 + 7358719 * 2 ^ 59
def prefixEnd_7358719 : Nat := 4983230072969 + 3 ^ 40 * 7358719 * 2
def baseEnd_7358719 : Nat := 1259519949457633237256791

theorem tailTrace_7358719 : CollatzResearch.WordTrace tailWord_7358719 prefixEnd_7358719 1259519949457633237256791 := by
  unfold tailWord_7358719
  simp only [CollatzResearch.WordTrace]
  refine ⟨268394531427625306993807211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178929687618416871329204807 268394531427625306993807211)
  ·
    refine ⟨402591797141437960490710817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268394531427625306993807211 402591797141437960490710817)
    ·
      refine ⟨301943847856078470368033113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402591797141437960490710817 301943847856078470368033113)
      ·
        refine ⟨226457885892058852776024835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301943847856078470368033113 226457885892058852776024835)
        ·
          refine ⟨339686828838088279164037253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226457885892058852776024835 339686828838088279164037253)
          ·
            refine ⟨63691280407141552343256985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339686828838088279164037253 63691280407141552343256985)
            ·
              refine ⟨47768460305356164257442739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63691280407141552343256985 47768460305356164257442739)
              ·
                refine ⟨71652690458034246386164109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47768460305356164257442739 71652690458034246386164109)
                ·
                  refine ⟨26869758921762842394811541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71652690458034246386164109 26869758921762842394811541)
                  ·
                    refine ⟨1259519949457633237256791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26869758921762842394811541 1259519949457633237256791)
                    ·
                      rfl

theorem cell23_7358719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 6].length) (baseStart_7358719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358719 prefixEnd_7358719 := by exact prefixLift 7358719
  have htrace : WordTrace (prefixWord ++ tailWord_7358719) baseStart_7358719 baseEnd_7358719 := by
    simpa [prefixWord, tailWord_7358719, baseEnd_7358719] using wordTrace_append hprefix tailTrace_7358719
  have hstable : (prefixWord ++ tailWord_7358719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358719).length < 2 ^ (prefixWord ++ tailWord_7358719).sum := by decide
  have hdescent : baseEnd_7358719 < baseStart_7358719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358720 : List Nat := [2, 1, 1, 2, 1, 1, 7, 3, 1, 1, 3]
def baseStart_7358720 : Nat := 118140960795 + 7358720 * 2 ^ 59
def prefixEnd_7358720 : Nat := 4983230072969 + 3 ^ 40 * 7358720 * 2
def baseEnd_7358720 : Nat := 3778560361853554207857869

theorem tailTrace_7358720 : CollatzResearch.WordTrace tailWord_7358720 prefixEnd_7358720 3778560361853554207857869 := by
  unfold tailWord_7358720
  simp only [CollatzResearch.WordTrace]
  refine ⟨134197283950310842082296807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178929711933747789443062409 134197283950310842082296807)
  ·
    refine ⟨201295925925466263123445211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134197283950310842082296807 201295925925466263123445211)
    ·
      refine ⟨301943888888199394685167817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201295925925466263123445211 301943888888199394685167817)
      ·
        refine ⟨226457916666149546013875863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301943888888199394685167817 226457916666149546013875863)
        ·
          refine ⟨339686874999224319020813795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226457916666149546013875863 339686874999224319020813795)
          ·
            refine ⟨509530312498836478531220693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339686874999224319020813795 509530312498836478531220693)
            ·
              refine ⟨11942116699191479965575485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 509530312498836478531220693 11942116699191479965575485)
              ·
                refine ⟨4478293762196804987090807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11942116699191479965575485 4478293762196804987090807)
                ·
                  refine ⟨6717440643295207480636211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4478293762196804987090807 6717440643295207480636211)
                  ·
                    refine ⟨10076160964942811220954317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6717440643295207480636211 10076160964942811220954317)
                    ·
                      refine ⟨3778560361853554207857869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10076160964942811220954317 3778560361853554207857869)
                      ·
                        rfl

theorem cell23_7358720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 1, 1, 3].length) (baseStart_7358720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358720 prefixEnd_7358720 := by exact prefixLift 7358720
  have htrace : WordTrace (prefixWord ++ tailWord_7358720) baseStart_7358720 baseEnd_7358720 := by
    simpa [prefixWord, tailWord_7358720, baseEnd_7358720] using wordTrace_append hprefix tailTrace_7358720
  have hstable : (prefixWord ++ tailWord_7358720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358720).length < 2 ^ (prefixWord ++ tailWord_7358720).sum := by decide
  have hdescent : baseEnd_7358720 < baseStart_7358720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358737 : List Nat := [1, 2, 2, 1, 1, 6, 3, 2, 1, 1, 3]
def baseStart_7358737 : Nat := 118140960795 + 7358737 * 2 ^ 59
def prefixEnd_7358737 : Nat := 4983230072969 + 3 ^ 40 * 7358737 * 2
def baseEnd_7358737 : Nat := 3778569091024680641345291

theorem tailTrace_7358737 : CollatzResearch.WordTrace tailWord_7358737 prefixEnd_7358737 3778569091024680641345291 := by
  unfold tailWord_7358737
  simp only [CollatzResearch.WordTrace]
  refine ⟨268395187941560096067962465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178930125294373397378641643 268395187941560096067962465)
  ·
    refine ⟨201296390956170072050971849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268395187941560096067962465 201296390956170072050971849)
    ·
      refine ⟨150972293217127554038228887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201296390956170072050971849 150972293217127554038228887)
      ·
        refine ⟨226458439825691331057343331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150972293217127554038228887 226458439825691331057343331)
        ·
          refine ⟨339687659738536996586014997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226458439825691331057343331 339687659738536996586014997)
          ·
            refine ⟨15922859050243921714969453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 339687659738536996586014997 15922859050243921714969453)
            ·
              refine ⟨5971072143841470643113545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15922859050243921714969453 5971072143841470643113545)
              ·
                refine ⟨4478304107881102982335159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5971072143841470643113545 4478304107881102982335159)
                ·
                  refine ⟨6717456161821654473502739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4478304107881102982335159 6717456161821654473502739)
                  ·
                    refine ⟨10076184242732481710254109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6717456161821654473502739 10076184242732481710254109)
                    ·
                      refine ⟨3778569091024680641345291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10076184242732481710254109 3778569091024680641345291)
                      ·
                        rfl

theorem cell23_7358737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 1, 1, 3].length) (baseStart_7358737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358737 prefixEnd_7358737 := by exact prefixLift 7358737
  have htrace : WordTrace (prefixWord ++ tailWord_7358737) baseStart_7358737 baseEnd_7358737 := by
    simpa [prefixWord, tailWord_7358737, baseEnd_7358737] using wordTrace_append hprefix tailTrace_7358737
  have hstable : (prefixWord ++ tailWord_7358737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358737).length < 2 ^ (prefixWord ++ tailWord_7358737).sum := by decide
  have hdescent : baseEnd_7358737 < baseStart_7358737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358756 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_7358756 : Nat := 118140960795 + 7358756 * 2 ^ 59
def prefixEnd_7358756 : Nat := 4983230072969 + 3 ^ 40 * 7358756 * 2
def baseEnd_7358756 : Nat := 3778578847157116067007703

theorem tailTrace_7358756 : CollatzResearch.WordTrace tailWord_7358756 prefixEnd_7358756 3778578847157116067007703 := by
  unfold tailWord_7358756
  simp only [CollatzResearch.WordTrace]
  refine ⟨134197940464245631156452061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178930587285660841541936081 134197940464245631156452061)
  ·
    refine ⟨50324227674092111683669523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134197940464245631156452061 50324227674092111683669523)
    ·
      refine ⟨75486341511138167525504285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50324227674092111683669523 75486341511138167525504285)
      ·
        refine ⟨28307378066676812822064107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75486341511138167525504285 28307378066676812822064107)
        ·
          refine ⟨42461067100015219233096161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28307378066676812822064107 42461067100015219233096161)
          ·
            refine ⟨31845800325011414424822121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42461067100015219233096161 31845800325011414424822121)
            ·
              refine ⟨23884350243758560818616591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31845800325011414424822121 23884350243758560818616591)
              ·
                refine ⟨35826525365637841227924887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23884350243758560818616591 35826525365637841227924887)
                ·
                  refine ⟨53739788048456761841887331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35826525365637841227924887 53739788048456761841887331)
                  ·
                    refine ⟨80609682072685142762830997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53739788048456761841887331 80609682072685142762830997)
                    ·
                      refine ⟨3778578847157116067007703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80609682072685142762830997 3778578847157116067007703)
                      ·
                        rfl

theorem cell23_7358756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_7358756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358756 prefixEnd_7358756 := by exact prefixLift 7358756
  have htrace : WordTrace (prefixWord ++ tailWord_7358756) baseStart_7358756 baseEnd_7358756 := by
    simpa [prefixWord, tailWord_7358756, baseEnd_7358756] using wordTrace_append hprefix tailTrace_7358756
  have hstable : (prefixWord ++ tailWord_7358756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358756).length < 2 ^ (prefixWord ++ tailWord_7358756).sum := by decide
  have hdescent : baseEnd_7358756 < baseStart_7358756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358776 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 3, 3, 3]
def baseStart_7358776 : Nat := 118140960795 + 7358776 * 2 ^ 59
def prefixEnd_7358776 : Nat := 4983230072969 + 3 ^ 40 * 7358776 * 2
def baseEnd_7358776 : Nat := 3778589116770205988757611

theorem tailTrace_7358776 : CollatzResearch.WordTrace tailWord_7358776 prefixEnd_7358776 3778589116770205988757611 := by
  unfold tailWord_7358776
  simp only [CollatzResearch.WordTrace]
  refine ⟨134198305194209402864316091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178931073592279203819088121 134198305194209402864316091)
  ·
    refine ⟨201297457791314104296474137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134198305194209402864316091 201297457791314104296474137)
    ·
      refine ⟨150973093343485578222355603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201297457791314104296474137 150973093343485578222355603)
      ·
        refine ⟨226459640015228367333533405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150973093343485578222355603 226459640015228367333533405)
        ·
          refine ⟨84922365005710637750075027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226459640015228367333533405 84922365005710637750075027)
          ·
            refine ⟨127383547508565956625112541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84922365005710637750075027 127383547508565956625112541)
            ·
              refine ⟨47768830315712233734417203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127383547508565956625112541 47768830315712233734417203)
              ·
                refine ⟨71653245473568350601625805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47768830315712233734417203 71653245473568350601625805)
                ·
                  refine ⟨26869967052588131475609677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71653245473568350601625805 26869967052588131475609677)
                  ·
                    refine ⟨10076237644720549303353629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26869967052588131475609677 10076237644720549303353629)
                    ·
                      refine ⟨3778589116770205988757611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10076237644720549303353629 3778589116770205988757611)
                      ·
                        rfl

theorem cell23_7358776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_7358776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358776 prefixEnd_7358776 := by exact prefixLift 7358776
  have htrace : WordTrace (prefixWord ++ tailWord_7358776) baseStart_7358776 baseEnd_7358776 := by
    simpa [prefixWord, tailWord_7358776, baseEnd_7358776] using wordTrace_append hprefix tailTrace_7358776
  have hstable : (prefixWord ++ tailWord_7358776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358776).length < 2 ^ (prefixWord ++ tailWord_7358776).sum := by decide
  have hdescent : baseEnd_7358776 < baseStart_7358776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358780 : List Nat := [2, 2, 2, 2, 1, 2, 5, 1, 1, 2, 3]
def baseStart_7358780 : Nat := 118140960795 + 7358780 * 2 ^ 59
def prefixEnd_7358780 : Nat := 4983230072969 + 3 ^ 40 * 7358780 * 2
def baseEnd_7358780 : Nat := 3778591170692823973107593

theorem tailTrace_7358780 : CollatzResearch.WordTrace tailWord_7358780 prefixEnd_7358780 3778591170692823973107593 := by
  unfold tailWord_7358780
  simp only [CollatzResearch.WordTrace]
  refine ⟨134198378140202157205888897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178931170853602876274518529 134198378140202157205888897)
  ·
    refine ⟨100648783605151617904416673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134198378140202157205888897 100648783605151617904416673)
    ·
      refine ⟨75486587703863713428312505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100648783605151617904416673 75486587703863713428312505)
      ·
        refine ⟨56614940777897785071234379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75486587703863713428312505 56614940777897785071234379)
        ·
          refine ⟨84922411166846677606851569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56614940777897785071234379 84922411166846677606851569)
          ·
            refine ⟨63691808375135008205138677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84922411166846677606851569 63691808375135008205138677)
            ·
              refine ⟨5971107035168907019231751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63691808375135008205138677 5971107035168907019231751)
              ·
                refine ⟨8956660552753360528847627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5971107035168907019231751 8956660552753360528847627)
                ·
                  refine ⟨13434990829130040793271441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8956660552753360528847627 13434990829130040793271441)
                  ·
                    refine ⟨10076243121847530594953581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13434990829130040793271441 10076243121847530594953581)
                    ·
                      refine ⟨3778591170692823973107593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10076243121847530594953581 3778591170692823973107593)
                      ·
                        rfl

theorem cell23_7358780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_7358780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358780 prefixEnd_7358780 := by exact prefixLift 7358780
  have htrace : WordTrace (prefixWord ++ tailWord_7358780) baseStart_7358780 baseEnd_7358780 := by
    simpa [prefixWord, tailWord_7358780, baseEnd_7358780] using wordTrace_append hprefix tailTrace_7358780
  have hstable : (prefixWord ++ tailWord_7358780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358780).length < 2 ^ (prefixWord ++ tailWord_7358780).sum := by decide
  have hdescent : baseEnd_7358780 < baseStart_7358780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358788 : List Nat := [2, 3, 4, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_7358788 : Nat := 118140960795 + 7358788 * 2 ^ 59
def prefixEnd_7358788 : Nat := 4983230072969 + 3 ^ 40 * 7358788 * 2
def baseEnd_7358788 : Nat := 3778595278538059941807557

theorem tailTrace_7358788 : CollatzResearch.WordTrace tailWord_7358788 prefixEnd_7358788 3778595278538059941807557 := by
  unfold tailWord_7358788
  simp only [CollatzResearch.WordTrace]
  refine ⟨134198524032187665889034509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178931365376250221185379345 134198524032187665889034509)
  ·
    refine ⟨50324446512070374708387941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134198524032187665889034509 50324446512070374708387941)
    ·
      refine ⟨9435833721013195257822739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50324446512070374708387941 9435833721013195257822739)
      ·
        refine ⟨14153750581519792886734109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9435833721013195257822739 14153750581519792886734109)
        ·
          refine ⟨5307656468069922332525291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14153750581519792886734109 5307656468069922332525291)
          ·
            refine ⟨7961484702104883498787937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307656468069922332525291 7961484702104883498787937)
            ·
              refine ⟨5971113526578662624090953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7961484702104883498787937 5971113526578662624090953)
              ·
                refine ⟨4478335144933996968068215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5971113526578662624090953 4478335144933996968068215)
                ·
                  refine ⟨6717502717400995452102323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4478335144933996968068215 6717502717400995452102323)
                  ·
                    refine ⟨10076254076101493178153485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6717502717400995452102323 10076254076101493178153485)
                    ·
                      refine ⟨3778595278538059941807557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10076254076101493178153485 3778595278538059941807557)
                      ·
                        rfl

theorem cell23_7358788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_7358788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358788 prefixEnd_7358788 := by exact prefixLift 7358788
  have htrace : WordTrace (prefixWord ++ tailWord_7358788) baseStart_7358788 baseEnd_7358788 := by
    simpa [prefixWord, tailWord_7358788, baseEnd_7358788] using wordTrace_append hprefix tailTrace_7358788
  have hstable : (prefixWord ++ tailWord_7358788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358788).length < 2 ^ (prefixWord ++ tailWord_7358788).sum := by decide
  have hdescent : baseEnd_7358788 < baseStart_7358788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358789 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_7358789 : Nat := 118140960795 + 7358789 * 2 ^ 59
def prefixEnd_7358789 : Nat := 4983230072969 + 3 ^ 40 * 7358789 * 2
def baseEnd_7358789 : Nat := 3778595792018714437895051

theorem tailTrace_7358789 : CollatzResearch.WordTrace tailWord_7358789 prefixEnd_7358789 3778595792018714437895051 := by
  unfold tailWord_7358789
  simp only [CollatzResearch.WordTrace]
  refine ⟨268397084537371708948855421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178931389691581139299236947 268397084537371708948855421)
  ·
    refine ⟨100648906701514390855820783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268397084537371708948855421 100648906701514390855820783)
    ·
      refine ⟨150973360052271586283731175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100648906701514390855820783 150973360052271586283731175)
      ·
        refine ⟨226460040078407379425596763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150973360052271586283731175 226460040078407379425596763)
        ·
          refine ⟨339690060117611069138395145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226460040078407379425596763 339690060117611069138395145)
          ·
            refine ⟨254767545088208301853796359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339690060117611069138395145 254767545088208301853796359)
            ·
              refine ⟨382151317632312452780694539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254767545088208301853796359 382151317632312452780694539)
              ·
                refine ⟨573226976448468679171041809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382151317632312452780694539 573226976448468679171041809)
                ·
                  refine ⟨429920232336351509378281357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573226976448468679171041809 429920232336351509378281357)
                  ·
                    refine ⟨161220087126131816016855509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 429920232336351509378281357 161220087126131816016855509)
                    ·
                      refine ⟨3778595792018714437895051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161220087126131816016855509 3778595792018714437895051)
                      ·
                        rfl

theorem cell23_7358789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_7358789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358789 prefixEnd_7358789 := by exact prefixLift 7358789
  have htrace : WordTrace (prefixWord ++ tailWord_7358789) baseStart_7358789 baseEnd_7358789 := by
    simpa [prefixWord, tailWord_7358789, baseEnd_7358789] using wordTrace_append hprefix tailTrace_7358789
  have hstable : (prefixWord ++ tailWord_7358789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358789).length < 2 ^ (prefixWord ++ tailWord_7358789).sum := by decide
  have hdescent : baseEnd_7358789 < baseStart_7358789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358820 : List Nat := [2, 3, 1, 1, 3, 1, 2, 4, 1, 3, 2]
def baseStart_7358820 : Nat := 118140960795 + 7358820 * 2 ^ 59
def prefixEnd_7358820 : Nat := 4983230072969 + 3 ^ 40 * 7358820 * 2
def baseEnd_7358820 : Nat := 3778611709919003816607409

theorem tailTrace_7358820 : CollatzResearch.WordTrace tailWord_7358820 prefixEnd_7358820 3778611709919003816607409 := by
  unfold tailWord_7358820
  simp only [CollatzResearch.WordTrace]
  refine ⟨134199107600129700621616957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178932143466839600828822609 134199107600129700621616957)
  ·
    refine ⟨50324665350048637733106359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134199107600129700621616957 50324665350048637733106359)
    ·
      refine ⟨75486998025072956599659539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50324665350048637733106359 75486998025072956599659539)
      ·
        refine ⟨113230497037609434899489309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75486998025072956599659539 113230497037609434899489309)
        ·
          refine ⟨42461436389103538087308491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113230497037609434899489309 42461436389103538087308491)
          ·
            refine ⟨63692154583655307130962737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42461436389103538087308491 63692154583655307130962737)
            ·
              refine ⟨47769115937741480348222053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63692154583655307130962737 47769115937741480348222053)
              ·
                refine ⟨8956709238326527565291635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47769115937741480348222053 8956709238326527565291635)
                ·
                  refine ⟨13435063857489791347937453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8956709238326527565291635 13435063857489791347937453)
                  ·
                    refine ⟨5038148946558671755476545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13435063857489791347937453 5038148946558671755476545)
                    ·
                      refine ⟨3778611709919003816607409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5038148946558671755476545 3778611709919003816607409)
                      ·
                        rfl

theorem cell23_7358820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_7358820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358820 prefixEnd_7358820 := by exact prefixLift 7358820
  have htrace : WordTrace (prefixWord ++ tailWord_7358820) baseStart_7358820 baseEnd_7358820 := by
    simpa [prefixWord, tailWord_7358820, baseEnd_7358820] using wordTrace_append hprefix tailTrace_7358820
  have hstable : (prefixWord ++ tailWord_7358820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358820).length < 2 ^ (prefixWord ++ tailWord_7358820).sum := by decide
  have hdescent : baseEnd_7358820 < baseStart_7358820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358837 : List Nat := [1, 3, 4, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_7358837 : Nat := 118140960795 + 7358837 * 2 ^ 59
def prefixEnd_7358837 : Nat := 4983230072969 + 3 ^ 40 * 7358837 * 2
def baseEnd_7358837 : Nat := 3778620439090130250094831

theorem tailTrace_7358837 : CollatzResearch.WordTrace tailWord_7358837 prefixEnd_7358837 3778620439090130250094831 := by
  unfold tailWord_7358837
  simp only [CollatzResearch.WordTrace]
  refine ⟨268398835241197813146602765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178932556827465208764401843 268398835241197813146602765)
  ·
    refine ⟨100649563215449179929976037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268398835241197813146602765 100649563215449179929976037)
    ·
      refine ⟨18871793102896721236870507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100649563215449179929976037 18871793102896721236870507)
      ·
        refine ⟨28307689654345081855305761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18871793102896721236870507 28307689654345081855305761)
        ·
          refine ⟨21230767240758811391479321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28307689654345081855305761 21230767240758811391479321)
          ·
            refine ⟨15923075430569108543609491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21230767240758811391479321 15923075430569108543609491)
            ·
              refine ⟨23884613145853662815414237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15923075430569108543609491 23884613145853662815414237)
              ·
                refine ⟨8956729929695123555780339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23884613145853662815414237 8956729929695123555780339)
                ·
                  refine ⟨13435094894542685333670509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8956729929695123555780339 13435094894542685333670509)
                  ·
                    refine ⟨5038160585453507000126441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13435094894542685333670509 5038160585453507000126441)
                    ·
                      refine ⟨3778620439090130250094831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5038160585453507000126441 3778620439090130250094831)
                      ·
                        rfl

theorem cell23_7358837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_7358837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358837 prefixEnd_7358837 := by exact prefixLift 7358837
  have htrace : WordTrace (prefixWord ++ tailWord_7358837) baseStart_7358837 baseEnd_7358837 := by
    simpa [prefixWord, tailWord_7358837, baseEnd_7358837] using wordTrace_append hprefix tailTrace_7358837
  have hstable : (prefixWord ++ tailWord_7358837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358837).length < 2 ^ (prefixWord ++ tailWord_7358837).sum := by decide
  have hdescent : baseEnd_7358837 < baseStart_7358837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358903 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 2, 5]
def baseStart_7358903 : Nat := 118140960795 + 7358903 * 2 ^ 59
def prefixEnd_7358903 : Nat := 4983230072969 + 3 ^ 40 * 7358903 * 2
def baseEnd_7358903 : Nat := 1259551442937775663956509

theorem tailTrace_7358903 : CollatzResearch.WordTrace tailWord_7358903 prefixEnd_7358903 1259551442937775663956509 := by
  unfold tailWord_7358903
  simp only [CollatzResearch.WordTrace]
  refine ⟨268401242458958706418505363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178934161639305804279003575 268401242458958706418505363)
  ·
    refine ⟨402601863688438059627758045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268401242458958706418505363 402601863688438059627758045)
    ·
      refine ⟨150975698883164272360409267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402601863688438059627758045 150975698883164272360409267)
      ·
        refine ⟨226463548324746408540613901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150975698883164272360409267 226463548324746408540613901)
        ·
          refine ⟨84923830621779903202730213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226463548324746408540613901 84923830621779903202730213)
          ·
            refine ⟨15923218241583731850511915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84923830621779903202730213 15923218241583731850511915)
            ·
              refine ⟨23884827362375597775767873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15923218241583731850511915 23884827362375597775767873)
              ·
                refine ⟨17913620521781698331825905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23884827362375597775767873 17913620521781698331825905)
                ·
                  refine ⟨13435215391336273748869429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17913620521781698331825905 13435215391336273748869429)
                  ·
                    refine ⟨1259551442937775663956509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13435215391336273748869429 1259551442937775663956509)
                    ·
                      rfl

theorem cell23_7358903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_7358903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358903 prefixEnd_7358903 := by exact prefixLift 7358903
  have htrace : WordTrace (prefixWord ++ tailWord_7358903) baseStart_7358903 baseEnd_7358903 := by
    simpa [prefixWord, tailWord_7358903, baseEnd_7358903] using wordTrace_append hprefix tailTrace_7358903
  have hstable : (prefixWord ++ tailWord_7358903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358903).length < 2 ^ (prefixWord ++ tailWord_7358903).sum := by decide
  have hdescent : baseEnd_7358903 < baseStart_7358903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358923 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 1, 6, 2]
def baseStart_7358923 : Nat := 118140960795 + 7358923 * 2 ^ 59
def prefixEnd_7358923 : Nat := 4983230072969 + 3 ^ 40 * 7358923 * 2
def baseEnd_7358923 : Nat := 3778664598426416913619435

theorem tailTrace_7358923 : CollatzResearch.WordTrace tailWord_7358923 prefixEnd_7358923 3778664598426416913619435 := by
  unfold tailWord_7358923
  simp only [CollatzResearch.WordTrace]
  refine ⟨268401971918886249834233423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178934647945924166556155615 268401971918886249834233423)
  ·
    refine ⟨402602957878329374751350135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268401971918886249834233423 402602957878329374751350135)
    ·
      refine ⟨603904436817494062127025203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402602957878329374751350135 603904436817494062127025203)
      ·
        refine ⟨905856655226241093190537805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603904436817494062127025203 905856655226241093190537805)
        ·
          refine ⟨339696245709840409946451677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 905856655226241093190537805 339696245709840409946451677)
          ·
            refine ⟨127386092141190153729919379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339696245709840409946451677 127386092141190153729919379)
            ·
              refine ⟨191079138211785230594879069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127386092141190153729919379 191079138211785230594879069)
              ·
                refine ⟨71654676829419461473079651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191079138211785230594879069 71654676829419461473079651)
                ·
                  refine ⟨107482015244129192209619477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71654676829419461473079651 107482015244129192209619477)
                  ·
                    refine ⟨5038219464568555884825913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107482015244129192209619477 5038219464568555884825913)
                    ·
                      refine ⟨3778664598426416913619435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5038219464568555884825913 3778664598426416913619435)
                      ·
                        rfl

theorem cell23_7358923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 6, 2].length) (baseStart_7358923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358923 prefixEnd_7358923 := by exact prefixLift 7358923
  have htrace : WordTrace (prefixWord ++ tailWord_7358923) baseStart_7358923 baseEnd_7358923 := by
    simpa [prefixWord, tailWord_7358923, baseEnd_7358923] using wordTrace_append hprefix tailTrace_7358923
  have hstable : (prefixWord ++ tailWord_7358923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358923).length < 2 ^ (prefixWord ++ tailWord_7358923).sum := by decide
  have hdescent : baseEnd_7358923 < baseStart_7358923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358936 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_7358936 : Nat := 118140960795 + 7358936 * 2 ^ 59
def prefixEnd_7358936 : Nat := 4983230072969 + 3 ^ 40 * 7358936 * 2
def baseEnd_7358936 : Nat := 3778671273674925362756875

theorem tailTrace_7358936 : CollatzResearch.WordTrace tailWord_7358936 prefixEnd_7358936 3778671273674925362756875 := by
  unfold tailWord_7358936
  simp only [CollatzResearch.WordTrace]
  refine ⟨134201223033919576527228331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178934964045226102036304441 134201223033919576527228331)
  ·
    refine ⟨201301834550879364790842497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134201223033919576527228331 201301834550879364790842497)
    ·
      refine ⟨150976375913159523593131873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201301834550879364790842497 150976375913159523593131873)
      ·
        refine ⟨113232281934869642694848905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150976375913159523593131873 113232281934869642694848905)
        ·
          refine ⟨84924211451152232021136679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113232281934869642694848905 84924211451152232021136679)
          ·
            refine ⟨127386317176728348031705019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84924211451152232021136679 127386317176728348031705019)
            ·
              refine ⟨191079475765092522047557529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127386317176728348031705019 191079475765092522047557529)
              ·
                refine ⟨143309606823819391535668147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191079475765092522047557529 143309606823819391535668147)
                ·
                  refine ⟨214964410235729087303502221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143309606823819391535668147 214964410235729087303502221)
                  ·
                    refine ⟨80611653838398407738813333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214964410235729087303502221 80611653838398407738813333)
                    ·
                      refine ⟨3778671273674925362756875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80611653838398407738813333 3778671273674925362756875)
                      ·
                        rfl

theorem cell23_7358936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_7358936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358936 prefixEnd_7358936 := by exact prefixLift 7358936
  have htrace : WordTrace (prefixWord ++ tailWord_7358936) baseStart_7358936 baseEnd_7358936 := by
    simpa [prefixWord, tailWord_7358936, baseEnd_7358936] using wordTrace_append hprefix tailTrace_7358936
  have hstable : (prefixWord ++ tailWord_7358936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358936).length < 2 ^ (prefixWord ++ tailWord_7358936).sum := by decide
  have hdescent : baseEnd_7358936 < baseStart_7358936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358963 : List Nat := [1, 1, 1, 2, 2, 2, 6, 2, 6]
def baseStart_7358963 : Nat := 118140960795 + 7358963 * 2 ^ 59
def prefixEnd_7358963 : Nat := 4983230072969 + 3 ^ 40 * 7358963 * 2
def baseEnd_7358963 : Nat := 419853904183621861902139

theorem tailTrace_7358963 : CollatzResearch.WordTrace tailWord_7358963 prefixEnd_7358963 419853904183621861902139 := by
  unfold tailWord_7358963
  simp only [CollatzResearch.WordTrace]
  refine ⟨268403430838741336665689543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178935620559160891110459695 268403430838741336665689543)
  ·
    refine ⟨402605146258112004998534315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268403430838741336665689543 402605146258112004998534315)
    ·
      refine ⟨603907719387168007497801473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402605146258112004998534315 603907719387168007497801473)
      ·
        refine ⟨452930789540376005623351105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 603907719387168007497801473 452930789540376005623351105)
        ·
          refine ⟨339698092155282004217513329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452930789540376005623351105 339698092155282004217513329)
          ·
            refine ⟨254773569116461503163134997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339698092155282004217513329 254773569116461503163134997)
            ·
              refine ⟨11942511052334132960771953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 254773569116461503163134997 11942511052334132960771953)
              ·
                refine ⟨8956883289250599720578965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11942511052334132960771953 8956883289250599720578965)
                ·
                  refine ⟨419853904183621861902139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8956883289250599720578965 419853904183621861902139)
                  ·
                    rfl

theorem cell23_7358963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 6].length) (baseStart_7358963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358963 prefixEnd_7358963 := by exact prefixLift 7358963
  have htrace : WordTrace (prefixWord ++ tailWord_7358963) baseStart_7358963 baseEnd_7358963 := by
    simpa [prefixWord, tailWord_7358963, baseEnd_7358963] using wordTrace_append hprefix tailTrace_7358963
  have hstable : (prefixWord ++ tailWord_7358963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358963).length < 2 ^ (prefixWord ++ tailWord_7358963).sum := by decide
  have hdescent : baseEnd_7358963 < baseStart_7358963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358980 : List Nat := [2, 3, 2, 3, 1, 1, 2, 3, 6]
def baseStart_7358980 : Nat := 118140960795 + 7358980 * 2 ^ 59
def prefixEnd_7358980 : Nat := 4983230072969 + 3 ^ 40 * 7358980 * 2
def baseEnd_7358980 : Nat := 419854874091524798956297

theorem tailTrace_7358980 : CollatzResearch.WordTrace tailWord_7358980 prefixEnd_7358980 419854874091524798956297 := by
  unfold tailWord_7358980
  simp only [CollatzResearch.WordTrace]
  refine ⟨134202025439839874284529197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178936033919786499046038929 134202025439839874284529197)
  ·
    refine ⟨50325759539939952856698449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134202025439839874284529197 50325759539939952856698449)
    ·
      refine ⟨37744319654954964642523837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50325759539939952856698449 37744319654954964642523837)
      ·
        refine ⟨14154119870608111740946439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37744319654954964642523837 14154119870608111740946439)
        ·
          refine ⟨21231179805912167611419659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14154119870608111740946439 21231179805912167611419659)
          ·
            refine ⟨31846769708868251417129489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21231179805912167611419659 31846769708868251417129489)
            ·
              refine ⟨23885077281651188562847117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31846769708868251417129489 23885077281651188562847117)
              ·
                refine ⟨8956903980619195711067669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23885077281651188562847117 8956903980619195711067669)
                ·
                  refine ⟨419854874091524798956297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8956903980619195711067669 419854874091524798956297)
                  ·
                    rfl

theorem cell23_7358980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_7358980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7358980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7358980 prefixEnd_7358980 := by exact prefixLift 7358980
  have htrace : WordTrace (prefixWord ++ tailWord_7358980) baseStart_7358980 baseEnd_7358980 := by
    simpa [prefixWord, tailWord_7358980, baseEnd_7358980] using wordTrace_append hprefix tailTrace_7358980
  have hstable : (prefixWord ++ tailWord_7358980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358980).length < 2 ^ (prefixWord ++ tailWord_7358980).sum := by decide
  have hdescent : baseEnd_7358980 < baseStart_7358980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359040 : List Nat := [2, 1, 1, 2, 2, 2, 2, 5, 2, 4]
def baseStart_7359040 : Nat := 118140960795 + 7359040 * 2 ^ 59
def prefixEnd_7359040 : Nat := 4983230072969 + 3 ^ 40 * 7359040 * 2
def baseEnd_7359040 : Nat := 1259574891887664318618799

theorem tailTrace_7359040 : CollatzResearch.WordTrace tailWord_7359040 prefixEnd_7359040 1259574891887664318618799 := by
  unfold tailWord_7359040
  simp only [CollatzResearch.WordTrace]
  refine ⟨134203119629731189408121287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178937492839641585877495049 134203119629731189408121287)
  ·
    refine ⟨201304679444596784112181931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134203119629731189408121287 201304679444596784112181931)
    ·
      refine ⟨301957019166895176168272897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201304679444596784112181931 301957019166895176168272897)
      ·
        refine ⟨226467764375171382126204673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301957019166895176168272897 226467764375171382126204673)
        ·
          refine ⟨169850823281378536594653505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226467764375171382126204673 169850823281378536594653505)
          ·
            refine ⟨127388117461033902445990129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169850823281378536594653505 127388117461033902445990129)
            ·
              refine ⟨95541088095775426834492597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127388117461033902445990129 95541088095775426834492597)
              ·
                refine ⟨8956977008978946265733681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95541088095775426834492597 8956977008978946265733681)
                ·
                  refine ⟨6717732756734209699300261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8956977008978946265733681 6717732756734209699300261)
                  ·
                    refine ⟨1259574891887664318618799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6717732756734209699300261 1259574891887664318618799)
                    ·
                      rfl

theorem cell23_7359040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 2, 4].length) (baseStart_7359040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359040 prefixEnd_7359040 := by exact prefixLift 7359040
  have htrace : WordTrace (prefixWord ++ tailWord_7359040) baseStart_7359040 baseEnd_7359040 := by
    simpa [prefixWord, tailWord_7359040, baseEnd_7359040] using wordTrace_append hprefix tailTrace_7359040
  have hstable : (prefixWord ++ tailWord_7359040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359040).length < 2 ^ (prefixWord ++ tailWord_7359040).sum := by decide
  have hdescent : baseEnd_7359040 < baseStart_7359040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359047 : List Nat := [1, 1, 4, 1, 4, 2, 2, 2, 1, 1, 4]
def baseStart_7359047 : Nat := 118140960795 + 7359047 * 2 ^ 59
def prefixEnd_7359047 : Nat := 4983230072969 + 3 ^ 40 * 7359047 * 2
def baseEnd_7359047 : Nat := 3778728270027574428468865

theorem tailTrace_7359047 : CollatzResearch.WordTrace tailWord_7359047 prefixEnd_7359047 3778728270027574428468865 := by
  unfold tailWord_7359047
  simp only [CollatzResearch.WordTrace]
  refine ⟨268406494570437019011747395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178937663046958012674498263 268406494570437019011747395)
  ·
    refine ⟨402609741855655528517621093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268406494570437019011747395 402609741855655528517621093)
    ·
      refine ⟨75489326597935411597053955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 402609741855655528517621093 75489326597935411597053955)
      ·
        refine ⟨113233989896903117395580933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75489326597935411597053955 113233989896903117395580933)
        ·
          refine ⟨21231373105669334511671425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113233989896903117395580933 21231373105669334511671425)
          ·
            refine ⟨15923529829252000883753569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21231373105669334511671425 15923529829252000883753569)
            ·
              refine ⟨11942647371939000662815177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15923529829252000883753569 11942647371939000662815177)
              ·
                refine ⟨8956985528954250497111383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11942647371939000662815177 8956985528954250497111383)
                ·
                  refine ⟨13435478293431375745667075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8956985528954250497111383 13435478293431375745667075)
                  ·
                    refine ⟨20153217440147063618500613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13435478293431375745667075 20153217440147063618500613)
                    ·
                      refine ⟨3778728270027574428468865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20153217440147063618500613 3778728270027574428468865)
                      ·
                        rfl

theorem cell23_7359047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_7359047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359047 prefixEnd_7359047 := by exact prefixLift 7359047
  have htrace : WordTrace (prefixWord ++ tailWord_7359047) baseStart_7359047 baseEnd_7359047 := by
    simpa [prefixWord, tailWord_7359047, baseEnd_7359047] using wordTrace_append hprefix tailTrace_7359047
  have hstable : (prefixWord ++ tailWord_7359047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359047).length < 2 ^ (prefixWord ++ tailWord_7359047).sum := by decide
  have hdescent : baseEnd_7359047 < baseStart_7359047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359101 : List Nat := [1, 4, 1, 1, 6, 1, 1, 2, 1, 2, 3]
def baseStart_7359101 : Nat := 118140960795 + 7359101 * 2 ^ 59
def prefixEnd_7359101 : Nat := 4983230072969 + 3 ^ 40 * 7359101 * 2
def baseEnd_7359101 : Nat := 3778755997982917217193617

theorem tailTrace_7359101 : CollatzResearch.WordTrace tailWord_7359101 prefixEnd_7359101 3778755997982917217193617 := by
  unfold tailWord_7359101
  simp only [CollatzResearch.WordTrace]
  refine ⟨268408464112241386234213157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178938976074827590822808771 268408464112241386234213157)
  ·
    refine ⟨50326587021045259918914967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268408464112241386234213157 50326587021045259918914967)
    ·
      refine ⟨75489880531567889878372451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50326587021045259918914967 75489880531567889878372451)
      ·
        refine ⟨113234820797351834817558677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75489880531567889878372451 113234820797351834817558677)
        ·
          refine ⟨5307882224875867257073063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113234820797351834817558677 5307882224875867257073063)
          ·
            refine ⟨7961823337313800885609595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307882224875867257073063 7961823337313800885609595)
            ·
              refine ⟨11942735005970701328414393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7961823337313800885609595 11942735005970701328414393)
              ·
                refine ⟨8957051254478025996310795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11942735005970701328414393 8957051254478025996310795)
                ·
                  refine ⟨13435576881717038994466193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8957051254478025996310795 13435576881717038994466193)
                  ·
                    refine ⟨10076682661287779245849645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13435576881717038994466193 10076682661287779245849645)
                    ·
                      refine ⟨3778755997982917217193617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10076682661287779245849645 3778755997982917217193617)
                      ·
                        rfl

theorem cell23_7359101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_7359101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359101 prefixEnd_7359101 := by exact prefixLift 7359101
  have htrace : WordTrace (prefixWord ++ tailWord_7359101) baseStart_7359101 baseEnd_7359101 := by
    simpa [prefixWord, tailWord_7359101, baseEnd_7359101] using wordTrace_append hprefix tailTrace_7359101
  have hstable : (prefixWord ++ tailWord_7359101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359101).length < 2 ^ (prefixWord ++ tailWord_7359101).sum := by decide
  have hdescent : baseEnd_7359101 < baseStart_7359101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359103 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 4]
def baseStart_7359103 : Nat := 118140960795 + 7359103 * 2 ^ 59
def prefixEnd_7359103 : Nat := 4983230072969 + 3 ^ 40 * 7359103 * 2
def baseEnd_7359103 : Nat := 3778757024944226209368607

theorem tailTrace_7359103 : CollatzResearch.WordTrace tailWord_7359103 prefixEnd_7359103 3778757024944226209368607 := by
  unfold tailWord_7359103
  simp only [CollatzResearch.WordTrace]
  refine ⟨268408537058234140575785963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178939024705489427050523975 268408537058234140575785963)
  ·
    refine ⟨402612805587351210863678945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268408537058234140575785963 402612805587351210863678945)
    ·
      refine ⟨301959604190513408147759209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402612805587351210863678945 301959604190513408147759209)
      ·
        refine ⟨226469703142885056110819407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301959604190513408147759209 226469703142885056110819407)
        ·
          refine ⟨339704554714327584166229111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226469703142885056110819407 339704554714327584166229111)
          ·
            refine ⟨509556832071491376249343667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339704554714327584166229111 509556832071491376249343667)
            ·
              refine ⟨764335248107237064374015501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509556832071491376249343667 764335248107237064374015501)
              ·
                refine ⟨286625718040213899140255813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 764335248107237064374015501 286625718040213899140255813)
                ·
                  refine ⟨53742322132540106088797965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286625718040213899140255813 53742322132540106088797965)
                  ·
                    refine ⟨20153370799702539783299237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53742322132540106088797965 20153370799702539783299237)
                    ·
                      refine ⟨3778757024944226209368607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20153370799702539783299237 3778757024944226209368607)
                      ·
                        rfl

theorem cell23_7359103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_7359103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359103 prefixEnd_7359103 := by exact prefixLift 7359103
  have htrace : WordTrace (prefixWord ++ tailWord_7359103) baseStart_7359103 baseEnd_7359103 := by
    simpa [prefixWord, tailWord_7359103, baseEnd_7359103] using wordTrace_append hprefix tailTrace_7359103
  have hstable : (prefixWord ++ tailWord_7359103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359103).length < 2 ^ (prefixWord ++ tailWord_7359103).sum := by decide
  have hdescent : baseEnd_7359103 < baseStart_7359103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359113 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 4, 6]
def baseStart_7359113 : Nat := 118140960795 + 7359113 * 2 ^ 59
def prefixEnd_7359113 : Nat := 4983230072969 + 3 ^ 40 * 7359113 * 2
def baseEnd_7359113 : Nat := 1259587386583590390081187

theorem tailTrace_7359113 : CollatzResearch.WordTrace tailWord_7359113 prefixEnd_7359113 1259587386583590390081187 := by
  unfold tailWord_7359113
  simp only [CollatzResearch.WordTrace]
  refine ⟨268408901788197912283649993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178939267858798608189099995 268408901788197912283649993)
  ·
    refine ⟨201306676341148434212737495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268408901788197912283649993 201306676341148434212737495)
    ·
      refine ⟨301960014511722651319106243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201306676341148434212737495 301960014511722651319106243)
      ·
        refine ⟨452940021767583976978659365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301960014511722651319106243 452940021767583976978659365)
        ·
          refine ⟨84926254081421995683498631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 452940021767583976978659365 84926254081421995683498631)
          ·
            refine ⟨127389381122132993525247947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84926254081421995683498631 127389381122132993525247947)
            ·
              refine ⟨191084071683199490287871921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127389381122132993525247947 191084071683199490287871921)
              ·
                refine ⟨143313053762399617715903941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191084071683199490287871921 143313053762399617715903941)
                ·
                  refine ⟨26871197580449928321731989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143313053762399617715903941 26871197580449928321731989)
                  ·
                    refine ⟨1259587386583590390081187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26871197580449928321731989 1259587386583590390081187)
                    ·
                      rfl

theorem cell23_7359113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 6].length) (baseStart_7359113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359113 prefixEnd_7359113 := by exact prefixLift 7359113
  have htrace : WordTrace (prefixWord ++ tailWord_7359113) baseStart_7359113 baseEnd_7359113 := by
    simpa [prefixWord, tailWord_7359113, baseEnd_7359113] using wordTrace_append hprefix tailTrace_7359113
  have hstable : (prefixWord ++ tailWord_7359113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359113).length < 2 ^ (prefixWord ++ tailWord_7359113).sum := by decide
  have hdescent : baseEnd_7359113 < baseStart_7359113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359140 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_7359140 : Nat := 118140960795 + 7359140 * 2 ^ 59
def prefixEnd_7359140 : Nat := 4983230072969 + 3 ^ 40 * 7359140 * 2
def baseEnd_7359140 : Nat := 3778776023728442564605937

theorem tailTrace_7359140 : CollatzResearch.WordTrace tailWord_7359140 prefixEnd_7359140 3778776023728442564605937 := by
  unfold tailWord_7359140
  simp only [CollatzResearch.WordTrace]
  refine ⟨134204943279550047947441437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178939924372733397263255249 134204943279550047947441437)
  ·
    refine ⟨50326853729831267980290539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134204943279550047947441437 50326853729831267980290539)
    ·
      refine ⟨75490280594746901970435809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50326853729831267980290539 75490280594746901970435809)
      ·
        refine ⟨56617710446060176477826857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75490280594746901970435809 56617710446060176477826857)
        ·
          refine ⟨42463282834545132358370143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56617710446060176477826857 42463282834545132358370143)
          ·
            refine ⟨63694924251817698537555215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42463282834545132358370143 63694924251817698537555215)
            ·
              refine ⟨95542386377726547806332823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63694924251817698537555215 95542386377726547806332823)
              ·
                refine ⟨143313579566589821709499235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95542386377726547806332823 143313579566589821709499235)
                ·
                  refine ⟨214970369349884732564248853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143313579566589821709499235 214970369349884732564248853)
                  ·
                    refine ⟨10076736063275846838949165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 214970369349884732564248853 10076736063275846838949165)
                    ·
                      refine ⟨3778776023728442564605937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10076736063275846838949165 3778776023728442564605937)
                      ·
                        rfl

theorem cell23_7359140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_7359140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359140 prefixEnd_7359140 := by exact prefixLift 7359140
  have htrace : WordTrace (prefixWord ++ tailWord_7359140) baseStart_7359140 baseEnd_7359140 := by
    simpa [prefixWord, tailWord_7359140, baseEnd_7359140] using wordTrace_append hprefix tailTrace_7359140
  have hstable : (prefixWord ++ tailWord_7359140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359140).length < 2 ^ (prefixWord ++ tailWord_7359140).sum := by decide
  have hdescent : baseEnd_7359140 < baseStart_7359140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359247 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 3]
def baseStart_7359247 : Nat := 118140960795 + 7359247 * 2 ^ 59
def prefixEnd_7359247 : Nat := 4983230072969 + 3 ^ 40 * 7359247 * 2
def baseEnd_7359247 : Nat := 3778830966158473645967945

theorem tailTrace_7359247 : CollatzResearch.WordTrace tailWord_7359247 prefixEnd_7359247 3778830966158473645967945 := by
  unfold tailWord_7359247
  simp only [CollatzResearch.WordTrace]
  refine ⟨268413789169712453169027995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178942526113141635446018663 268413789169712453169027995)
  ·
    refine ⟨402620683754568679753541993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268413789169712453169027995 402620683754568679753541993)
    ·
      refine ⟨301965512815926509815156495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402620683754568679753541993 301965512815926509815156495)
      ·
        refine ⟨452948269223889764722734743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301965512815926509815156495 452948269223889764722734743)
        ·
          refine ⟨679422403835834647084102115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452948269223889764722734743 679422403835834647084102115)
          ·
            refine ⟨1019133605753751970626153173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679422403835834647084102115 1019133605753751970626153173)
            ·
              refine ⟨23885943884853561811550465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1019133605753751970626153173 23885943884853561811550465)
              ·
                refine ⟨17914457913640171358662849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23885943884853561811550465 17914457913640171358662849)
                ·
                  refine ⟨13435843435230128518997137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17914457913640171358662849 13435843435230128518997137)
                  ·
                    refine ⟨10076882576422596389247853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13435843435230128518997137 10076882576422596389247853)
                    ·
                      refine ⟨3778830966158473645967945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10076882576422596389247853 3778830966158473645967945)
                      ·
                        rfl

theorem cell23_7359247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 3].length) (baseStart_7359247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359247 prefixEnd_7359247 := by exact prefixLift 7359247
  have htrace : WordTrace (prefixWord ++ tailWord_7359247) baseStart_7359247 baseEnd_7359247 := by
    simpa [prefixWord, tailWord_7359247, baseEnd_7359247] using wordTrace_append hprefix tailTrace_7359247
  have hstable : (prefixWord ++ tailWord_7359247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359247).length < 2 ^ (prefixWord ++ tailWord_7359247).sum := by decide
  have hdescent : baseEnd_7359247 < baseStart_7359247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359304 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 2, 3, 2]
def baseStart_7359304 : Nat := 118140960795 + 7359304 * 2 ^ 59
def prefixEnd_7359304 : Nat := 4983230072969 + 3 ^ 40 * 7359304 * 2
def baseEnd_7359304 : Nat := 3778860234555779922955183

theorem tailTrace_7359304 : CollatzResearch.WordTrace tailWord_7359304 prefixEnd_7359304 3778860234555779922955183 := by
  unfold tailWord_7359304
  simp only [CollatzResearch.WordTrace]
  refine ⟨134207934065252975951926483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178943912087003967935901977 134207934065252975951926483)
  ·
    refine ⟨201311901097879463927889725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134207934065252975951926483 201311901097879463927889725)
    ·
      refine ⟨75491962911704798972958647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201311901097879463927889725 75491962911704798972958647)
      ·
        refine ⟨113237944367557198459437971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75491962911704798972958647 113237944367557198459437971)
        ·
          refine ⟨169856916551335797689156957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113237944367557198459437971 169856916551335797689156957)
          ·
            refine ⟨63696343706750924133433859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169856916551335797689156957 63696343706750924133433859)
            ·
              refine ⟨95544515560126386200150789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63696343706750924133433859 95544515560126386200150789)
              ·
                refine ⟨17914596667523697412528273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95544515560126386200150789 17914596667523697412528273)
                ·
                  refine ⟨13435947500642773059396205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17914596667523697412528273 13435947500642773059396205)
                  ·
                    refine ⟨5038480312741039897273577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13435947500642773059396205 5038480312741039897273577)
                    ·
                      refine ⟨3778860234555779922955183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5038480312741039897273577 3778860234555779922955183)
                      ·
                        rfl

theorem cell23_7359304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_7359304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359304 prefixEnd_7359304 := by exact prefixLift 7359304
  have htrace : WordTrace (prefixWord ++ tailWord_7359304) baseStart_7359304 baseEnd_7359304 := by
    simpa [prefixWord, tailWord_7359304, baseEnd_7359304] using wordTrace_append hprefix tailTrace_7359304
  have hstable : (prefixWord ++ tailWord_7359304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359304).length < 2 ^ (prefixWord ++ tailWord_7359304).sum := by decide
  have hdescent : baseEnd_7359304 < baseStart_7359304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359317 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_7359317 : Nat := 118140960795 + 7359317 * 2 ^ 59
def prefixEnd_7359317 : Nat := 4983230072969 + 3 ^ 40 * 7359317 * 2
def baseEnd_7359317 : Nat := 3778866909804288372092623

theorem tailTrace_7359317 : CollatzResearch.WordTrace tailWord_7359317 prefixEnd_7359317 3778866909804288372092623 := by
  unfold tailWord_7359317
  simp only [CollatzResearch.WordTrace]
  refine ⟨268416342279458855124076205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178944228186305903416050803 268416342279458855124076205)
  ·
    refine ⟨100656128354797070671528577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268416342279458855124076205 100656128354797070671528577)
    ·
      refine ⟨75492096266097803003646433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100656128354797070671528577 75492096266097803003646433)
      ·
        refine ⟨56619072199573352252734825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75492096266097803003646433 56619072199573352252734825)
        ·
          refine ⟨42464304149680014189551119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56619072199573352252734825 42464304149680014189551119)
          ·
            refine ⟨63696456224520021284326679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42464304149680014189551119 63696456224520021284326679)
            ·
              refine ⟨95544684336780031926490019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63696456224520021284326679 95544684336780031926490019)
              ·
                refine ⟨143317026505170047889735029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95544684336780031926490019 143317026505170047889735029)
                ·
                  refine ⟨13435971234859691989662659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143317026505170047889735029 13435971234859691989662659)
                  ·
                    refine ⟨20153956852289537984493989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13435971234859691989662659 20153956852289537984493989)
                    ·
                      refine ⟨3778866909804288372092623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20153956852289537984493989 3778866909804288372092623)
                      ·
                        rfl

theorem cell23_7359317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_7359317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359317 prefixEnd_7359317 := by exact prefixLift 7359317
  have htrace : WordTrace (prefixWord ++ tailWord_7359317) baseStart_7359317 baseEnd_7359317 := by
    simpa [prefixWord, tailWord_7359317, baseEnd_7359317] using wordTrace_append hprefix tailTrace_7359317
  have hstable : (prefixWord ++ tailWord_7359317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359317).length < 2 ^ (prefixWord ++ tailWord_7359317).sum := by decide
  have hdescent : baseEnd_7359317 < baseStart_7359317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359327 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 1, 6]
def baseStart_7359327 : Nat := 118140960795 + 7359327 * 2 ^ 59
def prefixEnd_7359327 : Nat := 4983230072969 + 3 ^ 40 * 7359327 * 2
def baseEnd_7359327 : Nat := 1259624014870277777655859

theorem tailTrace_7359327 : CollatzResearch.WordTrace tailWord_7359327 prefixEnd_7359327 1259624014870277777655859 := by
  unfold tailWord_7359327
  simp only [CollatzResearch.WordTrace]
  refine ⟨268416707009422626831940235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178944471339615084554626823 268416707009422626831940235)
  ·
    refine ⟨402625060514133940247910353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268416707009422626831940235 402625060514133940247910353)
    ·
      refine ⟨301968795385600455185932765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402625060514133940247910353 301968795385600455185932765)
      ·
        refine ⟨113238298269600170694724787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301968795385600455185932765 113238298269600170694724787)
        ·
          refine ⟨169857447404400256042087181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113238298269600170694724787 169857447404400256042087181)
          ·
            refine ⟨63696542776650096015782693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169857447404400256042087181 63696542776650096015782693)
            ·
              refine ⟨11943101770621893002959255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63696542776650096015782693 11943101770621893002959255)
              ·
                refine ⟨17914652655932839504438883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11943101770621893002959255 17914652655932839504438883)
                ·
                  refine ⟨26871978983899259256658325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17914652655932839504438883 26871978983899259256658325)
                  ·
                    refine ⟨1259624014870277777655859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26871978983899259256658325 1259624014870277777655859)
                    ·
                      rfl

theorem cell23_7359327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 6].length) (baseStart_7359327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359327 prefixEnd_7359327 := by exact prefixLift 7359327
  have htrace : WordTrace (prefixWord ++ tailWord_7359327) baseStart_7359327 baseEnd_7359327 := by
    simpa [prefixWord, tailWord_7359327, baseEnd_7359327] using wordTrace_append hprefix tailTrace_7359327
  have hstable : (prefixWord ++ tailWord_7359327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359327).length < 2 ^ (prefixWord ++ tailWord_7359327).sum := by decide
  have hdescent : baseEnd_7359327 < baseStart_7359327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359347 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 4]
def baseStart_7359347 : Nat := 118140960795 + 7359347 * 2 ^ 59
def prefixEnd_7359347 : Nat := 4983230072969 + 3 ^ 40 * 7359347 * 2
def baseEnd_7359347 : Nat := 3778882314223923254717485

theorem tailTrace_7359347 : CollatzResearch.WordTrace tailWord_7359347 prefixEnd_7359347 3778882314223923254717485 := by
  unfold tailWord_7359347
  simp only [CollatzResearch.WordTrace]
  refine ⟨268417436469350170247668295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178944957646233446831778863 268417436469350170247668295)
  ·
    refine ⟨402626154704025255371502443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268417436469350170247668295 402626154704025255371502443)
    ·
      refine ⟨603939232056037883057253665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402626154704025255371502443 603939232056037883057253665)
      ·
        refine ⟨452954424042028412292940249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 603939232056037883057253665 452954424042028412292940249)
        ·
          refine ⟨339715818031521309219705187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452954424042028412292940249 339715818031521309219705187)
          ·
            refine ⟨509573727047281963829557781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339715818031521309219705187 509573727047281963829557781)
            ·
              refine ⟨23886268455341342054510521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 509573727047281963829557781 23886268455341342054510521)
              ·
                refine ⟨17914701341506006540882891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23886268455341342054510521 17914701341506006540882891)
                ·
                  refine ⟨26872052012259009811324337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17914701341506006540882891 26872052012259009811324337)
                  ·
                    refine ⟨20154039009194257358493253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26872052012259009811324337 20154039009194257358493253)
                    ·
                      refine ⟨3778882314223923254717485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20154039009194257358493253 3778882314223923254717485)
                      ·
                        rfl

theorem cell23_7359347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_7359347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359347 prefixEnd_7359347 := by exact prefixLift 7359347
  have htrace : WordTrace (prefixWord ++ tailWord_7359347) baseStart_7359347 baseEnd_7359347 := by
    simpa [prefixWord, tailWord_7359347, baseEnd_7359347] using wordTrace_append hprefix tailTrace_7359347
  have hstable : (prefixWord ++ tailWord_7359347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359347).length < 2 ^ (prefixWord ++ tailWord_7359347).sum := by decide
  have hdescent : baseEnd_7359347 < baseStart_7359347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359368 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 3, 2, 2]
def baseStart_7359368 : Nat := 118140960795 + 7359368 * 2 ^ 59
def prefixEnd_7359368 : Nat := 4983230072969 + 3 ^ 40 * 7359368 * 2
def baseEnd_7359368 : Nat := 3778893097317667672554889

theorem tailTrace_7359368 : CollatzResearch.WordTrace tailWord_7359368 prefixEnd_7359368 3778893097317667672554889 := by
  unfold tailWord_7359368
  simp only [CollatzResearch.WordTrace]
  refine ⟨134209101201137045417091379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178945468268182727222788505 134209101201137045417091379)
  ·
    refine ⟨201313651801705568125637069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134209101201137045417091379 201313651801705568125637069)
    ·
      refine ⟨75492619425639588047113901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201313651801705568125637069 75492619425639588047113901)
      ·
        refine ⟨28309732284614845517667713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75492619425639588047113901 28309732284614845517667713)
        ·
          refine ⟨21232299213461134138250785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28309732284614845517667713 21232299213461134138250785)
          ·
            refine ⟨15924224410095850603688089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21232299213461134138250785 15924224410095850603688089)
            ·
              refine ⟨11943168307571887952766067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15924224410095850603688089 11943168307571887952766067)
              ·
                refine ⟨17914752461357831929149101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11943168307571887952766067 17914752461357831929149101)
                ·
                  refine ⟨6718032173009186973430913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17914752461357831929149101 6718032173009186973430913)
                  ·
                    refine ⟨5038524129756890230073185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6718032173009186973430913 5038524129756890230073185)
                    ·
                      refine ⟨3778893097317667672554889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5038524129756890230073185 3778893097317667672554889)
                      ·
                        rfl

theorem cell23_7359368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_7359368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359368 prefixEnd_7359368 := by exact prefixLift 7359368
  have htrace : WordTrace (prefixWord ++ tailWord_7359368) baseStart_7359368 baseEnd_7359368 := by
    simpa [prefixWord, tailWord_7359368, baseEnd_7359368] using wordTrace_append hprefix tailTrace_7359368
  have hstable : (prefixWord ++ tailWord_7359368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359368).length < 2 ^ (prefixWord ++ tailWord_7359368).sum := by decide
  have hdescent : baseEnd_7359368 < baseStart_7359368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359378 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 1, 6]
def baseStart_7359378 : Nat := 118140960795 + 7359378 * 2 ^ 59
def prefixEnd_7359378 : Nat := 4983230072969 + 3 ^ 40 * 7359378 * 2
def baseEnd_7359378 : Nat := 1259632744041404211143281

theorem tailTrace_7359378 : CollatzResearch.WordTrace tailWord_7359378 prefixEnd_7359378 1259632744041404211143281 := by
  unfold tailWord_7359378
  simp only [CollatzResearch.WordTrace]
  refine ⟨67104641783059465635511697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178945711421491908361364525 67104641783059465635511697)
  ·
    refine ⟨50328481337294599226633773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67104641783059465635511697 50328481337294599226633773)
    ·
      refine ⟨18873180501485474709987665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50328481337294599226633773 18873180501485474709987665)
      ·
        refine ⟨14154885376114106032490749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18873180501485474709987665 14154885376114106032490749)
        ·
          refine ⟨5308082016042789762184031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14154885376114106032490749 5308082016042789762184031)
          ·
            refine ⟨7962123024064184643276047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5308082016042789762184031 7962123024064184643276047)
            ·
              refine ⟨11943184536096276964914071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7962123024064184643276047 11943184536096276964914071)
              ·
                refine ⟨17914776804144415447371107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11943184536096276964914071 17914776804144415447371107)
                ·
                  refine ⟨26872165206216623171056661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17914776804144415447371107 26872165206216623171056661)
                  ·
                    refine ⟨1259632744041404211143281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26872165206216623171056661 1259632744041404211143281)
                    ·
                      rfl

theorem cell23_7359378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_7359378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359378 prefixEnd_7359378 := by exact prefixLift 7359378
  have htrace : WordTrace (prefixWord ++ tailWord_7359378) baseStart_7359378 baseEnd_7359378 := by
    simpa [prefixWord, tailWord_7359378, baseEnd_7359378] using wordTrace_append hprefix tailTrace_7359378
  have hstable : (prefixWord ++ tailWord_7359378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359378).length < 2 ^ (prefixWord ++ tailWord_7359378).sum := by decide
  have hdescent : baseEnd_7359378 < baseStart_7359378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359388 : List Nat := [2, 2, 3, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_7359388 : Nat := 118140960795 + 7359388 * 2 ^ 59
def prefixEnd_7359388 : Nat := 4983230072969 + 3 ^ 40 * 7359388 * 2
def baseEnd_7359388 : Nat := 3778903366930757594304797

theorem tailTrace_7359388 : CollatzResearch.WordTrace tailWord_7359388 prefixEnd_7359388 3778903366930757594304797 := by
  unfold tailWord_7359388
  simp only [CollatzResearch.WordTrace]
  refine ⟨134209465931100817124955409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178945954574801089499940545 134209465931100817124955409)
  ·
    refine ⟨100657099448325612843716557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134209465931100817124955409 100657099448325612843716557)
    ·
      refine ⟨37746412293122104816393709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100657099448325612843716557 37746412293122104816393709)
      ·
        refine ⟨14154904609920789306147641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37746412293122104816393709 14154904609920789306147641)
        ·
          refine ⟨10616178457440591979610731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14154904609920789306147641 10616178457440591979610731)
          ·
            refine ⟨15924267686160887969416097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10616178457440591979610731 15924267686160887969416097)
            ·
              refine ⟨11943200764620665977062073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15924267686160887969416097 11943200764620665977062073)
              ·
                refine ⟨8957400573465499482796555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11943200764620665977062073 8957400573465499482796555)
                ·
                  refine ⟨13436100860198249224194833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8957400573465499482796555 13436100860198249224194833)
                  ·
                    refine ⟨10077075645148686918146125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13436100860198249224194833 10077075645148686918146125)
                    ·
                      refine ⟨3778903366930757594304797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10077075645148686918146125 3778903366930757594304797)
                      ·
                        rfl

theorem cell23_7359388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_7359388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359388 prefixEnd_7359388 := by exact prefixLift 7359388
  have htrace : WordTrace (prefixWord ++ tailWord_7359388) baseStart_7359388 baseEnd_7359388 := by
    simpa [prefixWord, tailWord_7359388, baseEnd_7359388] using wordTrace_append hprefix tailTrace_7359388
  have hstable : (prefixWord ++ tailWord_7359388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359388).length < 2 ^ (prefixWord ++ tailWord_7359388).sum := by decide
  have hdescent : baseEnd_7359388 < baseStart_7359388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359427 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 3]
def baseStart_7359427 : Nat := 118140960795 + 7359427 * 2 ^ 59
def prefixEnd_7359427 : Nat := 4983230072969 + 3 ^ 40 * 7359427 * 2
def baseEnd_7359427 : Nat := 3778923392676282941717117

theorem tailTrace_7359427 : CollatzResearch.WordTrace tailWord_7359427 prefixEnd_7359427 3778923392676282941717117 := by
  unfold tailWord_7359427
  simp only [CollatzResearch.WordTrace]
  refine ⟨268420354309060343910580535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178946902872706895940387023 268420354309060343910580535)
  ·
    refine ⟨402630531463590515865870803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268420354309060343910580535 402630531463590515865870803)
    ·
      refine ⟨603945797195385773798806205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402630531463590515865870803 603945797195385773798806205)
      ·
        refine ⟨226479673948269665174552327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 603945797195385773798806205 226479673948269665174552327)
        ·
          refine ⟨339719510922404497761828491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226479673948269665174552327 339719510922404497761828491)
          ·
            refine ⟨509579266383606746642742737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339719510922404497761828491 509579266383606746642742737)
            ·
              refine ⟨382184449787705059982057053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509579266383606746642742737 382184449787705059982057053)
              ·
                refine ⟨143319168670389397493271395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382184449787705059982057053 143319168670389397493271395)
                ·
                  refine ⟨214978753005584096239907093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143319168670389397493271395 214978753005584096239907093)
                  ·
                    refine ⟨10077129047136754511245645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 214978753005584096239907093 10077129047136754511245645)
                    ·
                      refine ⟨3778923392676282941717117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10077129047136754511245645 3778923392676282941717117)
                      ·
                        rfl

theorem cell23_7359427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_7359427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359427 prefixEnd_7359427 := by exact prefixLift 7359427
  have htrace : WordTrace (prefixWord ++ tailWord_7359427) baseStart_7359427 baseEnd_7359427 := by
    simpa [prefixWord, tailWord_7359427, baseEnd_7359427] using wordTrace_append hprefix tailTrace_7359427
  have hstable : (prefixWord ++ tailWord_7359427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359427).length < 2 ^ (prefixWord ++ tailWord_7359427).sum := by decide
  have hdescent : baseEnd_7359427 < baseStart_7359427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359444 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_7359444 : Nat := 118140960795 + 7359444 * 2 ^ 59
def prefixEnd_7359444 : Nat := 4983230072969 + 3 ^ 40 * 7359444 * 2
def baseEnd_7359444 : Nat := 3778932121847409375204539

theorem tailTrace_7359444 : CollatzResearch.WordTrace tailWord_7359444 prefixEnd_7359444 3778932121847409375204539 := by
  unfold tailWord_7359444
  simp only [CollatzResearch.WordTrace]
  refine ⟨134210487174999377906974693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178947316233332503875966257 134210487174999377906974693)
  ·
    refine ⟨25164466345312383357557755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134210487174999377906974693 25164466345312383357557755)
    ·
      refine ⟨37746699517968575036336633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25164466345312383357557755 37746699517968575036336633)
      ·
        refine ⟨28310024638476431277252475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37746699517968575036336633 28310024638476431277252475)
        ·
          refine ⟨42465036957714646915878713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28310024638476431277252475 42465036957714646915878713)
          ·
            refine ⟨31848777718285985186909035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42465036957714646915878713 31848777718285985186909035)
            ·
              refine ⟨47773166577428977780363553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31848777718285985186909035 47773166577428977780363553)
              ·
                refine ⟨35829874933071733335272665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47773166577428977780363553 35829874933071733335272665)
                ·
                  refine ⟨26872406199803800001454499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35829874933071733335272665 26872406199803800001454499)
                  ·
                    refine ⟨40308609299705700002181749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26872406199803800001454499 40308609299705700002181749)
                    ·
                      refine ⟨3778932121847409375204539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40308609299705700002181749 3778932121847409375204539)
                      ·
                        rfl

theorem cell23_7359444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_7359444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359444 prefixEnd_7359444 := by exact prefixLift 7359444
  have htrace : WordTrace (prefixWord ++ tailWord_7359444) baseStart_7359444 baseEnd_7359444 := by
    simpa [prefixWord, tailWord_7359444, baseEnd_7359444] using wordTrace_append hprefix tailTrace_7359444
  have hstable : (prefixWord ++ tailWord_7359444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359444).length < 2 ^ (prefixWord ++ tailWord_7359444).sum := by decide
  have hdescent : baseEnd_7359444 < baseStart_7359444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359445 : List Nat := [1, 3, 2, 3, 3, 2, 1, 2, 1, 3, 2]
def baseStart_7359445 : Nat := 118140960795 + 7359445 * 2 ^ 59
def prefixEnd_7359445 : Nat := 4983230072969 + 3 ^ 40 * 7359445 * 2
def baseEnd_7359445 : Nat := 3778932635328063871292035

theorem tailTrace_7359445 : CollatzResearch.WordTrace tailWord_7359445 prefixEnd_7359445 3778932635328063871292035 := by
  unfold tailWord_7359445
  simp only [CollatzResearch.WordTrace]
  refine ⟨268421010822995132984735789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178947340548663421989823859 268421010822995132984735789)
  ·
    refine ⟨100657879058623174869275921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268421010822995132984735789 100657879058623174869275921)
    ·
      refine ⟨75493409293967381151956941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100657879058623174869275921 75493409293967381151956941)
      ·
        refine ⟨28310028485237767931983853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75493409293967381151956941 28310028485237767931983853)
        ·
          refine ⟨10616260681964162974493945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28310028485237767931983853 10616260681964162974493945)
          ·
            refine ⟨7962195511473122230870459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10616260681964162974493945 7962195511473122230870459)
            ·
              refine ⟨11943293267209683346305689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7962195511473122230870459 11943293267209683346305689)
              ·
                refine ⟨8957469950407262509729267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11943293267209683346305689 8957469950407262509729267)
                ·
                  refine ⟨13436204925610893764593901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8957469950407262509729267 13436204925610893764593901)
                  ·
                    refine ⟨5038576847104085161722713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13436204925610893764593901 5038576847104085161722713)
                    ·
                      refine ⟨3778932635328063871292035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5038576847104085161722713 3778932635328063871292035)
                      ·
                        rfl

theorem cell23_7359445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_7359445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359445 prefixEnd_7359445 := by exact prefixLift 7359445
  have htrace : WordTrace (prefixWord ++ tailWord_7359445) baseStart_7359445 baseEnd_7359445 := by
    simpa [prefixWord, tailWord_7359445, baseEnd_7359445] using wordTrace_append hprefix tailTrace_7359445
  have hstable : (prefixWord ++ tailWord_7359445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359445).length < 2 ^ (prefixWord ++ tailWord_7359445).sum := by decide
  have hdescent : baseEnd_7359445 < baseStart_7359445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359458 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_7359458 : Nat := 118140960795 + 7359458 * 2 ^ 59
def prefixEnd_7359458 : Nat := 4983230072969 + 3 ^ 40 * 7359458 * 2
def baseEnd_7359458 : Nat := 3778939310576572320429475

theorem tailTrace_7359458 : CollatzResearch.WordTrace tailWord_7359458 prefixEnd_7359458 3778939310576572320429475 := by
  unfold tailWord_7359458
  simp only [CollatzResearch.WordTrace]
  refine ⟨67105371242987009051239757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178947656647965357469972685 67105371242987009051239757)
  ·
    refine ⟨25164514216120128394214909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67105371242987009051239757 25164514216120128394214909)
    ·
      refine ⟨9436692831045048147830591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25164514216120128394214909 9436692831045048147830591)
      ·
        refine ⟨14155039246567572221745887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9436692831045048147830591 14155039246567572221745887)
        ·
          refine ⟨21232558869851358332618831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14155039246567572221745887 21232558869851358332618831)
          ·
            refine ⟨31848838304777037498928247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21232558869851358332618831 31848838304777037498928247)
            ·
              refine ⟨47773257457165556248392371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31848838304777037498928247 47773257457165556248392371)
              ·
                refine ⟨71659886185748334372588557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47773257457165556248392371 71659886185748334372588557)
                ·
                  refine ⟨26872457319655625389720709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71659886185748334372588557 26872457319655625389720709)
                  ·
                    refine ⟨5038585747435429760572633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26872457319655625389720709 5038585747435429760572633)
                    ·
                      refine ⟨3778939310576572320429475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5038585747435429760572633 3778939310576572320429475)
                      ·
                        rfl

theorem cell23_7359458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_7359458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359458 prefixEnd_7359458 := by exact prefixLift 7359458
  have htrace : WordTrace (prefixWord ++ tailWord_7359458) baseStart_7359458 baseEnd_7359458 := by
    simpa [prefixWord, tailWord_7359458, baseEnd_7359458] using wordTrace_append hprefix tailTrace_7359458
  have hstable : (prefixWord ++ tailWord_7359458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359458).length < 2 ^ (prefixWord ++ tailWord_7359458).sum := by decide
  have hdescent : baseEnd_7359458 < baseStart_7359458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359511 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 2, 5]
def baseStart_7359511 : Nat := 118140960795 + 7359511 * 2 ^ 59
def prefixEnd_7359511 : Nat := 4983230072969 + 3 ^ 40 * 7359511 * 2
def baseEnd_7359511 : Nat := 1259655508350420204355577

theorem tailTrace_7359511 : CollatzResearch.WordTrace tailWord_7359511 prefixEnd_7359511 1259655508350420204355577 := by
  unfold tailWord_7359511
  simp only [CollatzResearch.WordTrace]
  refine ⟨268423418040756026256638387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178948945360504017504425591 268423418040756026256638387)
  ·
    refine ⟨402635127061134039384957581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268423418040756026256638387 402635127061134039384957581)
    ·
      refine ⟨150988172647925264769359093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402635127061134039384957581 150988172647925264769359093)
      ·
        refine ⟨14155141185742993572127415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150988172647925264769359093 14155141185742993572127415)
        ·
          refine ⟨21232711778614490358191123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14155141185742993572127415 21232711778614490358191123)
          ·
            refine ⟨31849067667921735537286685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21232711778614490358191123 31849067667921735537286685)
            ·
              refine ⟨11943400375470650826482507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31849067667921735537286685 11943400375470650826482507)
              ·
                refine ⟨17915100563205976239723761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11943400375470650826482507 17915100563205976239723761)
                ·
                  refine ⟨13436325422404482179792821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17915100563205976239723761 13436325422404482179792821)
                  ·
                    refine ⟨1259655508350420204355577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13436325422404482179792821 1259655508350420204355577)
                    ·
                      rfl

theorem cell23_7359511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_7359511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359511 prefixEnd_7359511 := by exact prefixLift 7359511
  have htrace : WordTrace (prefixWord ++ tailWord_7359511) baseStart_7359511 baseEnd_7359511 := by
    simpa [prefixWord, tailWord_7359511, baseEnd_7359511] using wordTrace_append hprefix tailTrace_7359511
  have hstable : (prefixWord ++ tailWord_7359511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359511).length < 2 ^ (prefixWord ++ tailWord_7359511).sum := by decide
  have hdescent : baseEnd_7359511 < baseStart_7359511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359514 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_7359514 : Nat := 118140960795 + 7359514 * 2 ^ 59
def prefixEnd_7359514 : Nat := 4983230072969 + 3 ^ 40 * 7359514 * 2
def baseEnd_7359514 : Nat := 3778968065493224101329217

theorem tailTrace_7359514 : CollatzResearch.WordTrace tailWord_7359514 prefixEnd_7359514 3778968065493224101329217 := by
  unfold tailWord_7359514
  simp only [CollatzResearch.WordTrace]
  refine ⟨67105881864936289442249399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178949018306496771845998397 67105881864936289442249399)
  ·
    refine ⟨100658822797404434163374099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67105881864936289442249399 100658822797404434163374099)
    ·
      refine ⟨150988234196106651245061149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100658822797404434163374099 150988234196106651245061149)
      ·
        refine ⟨56620587823539994216897931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150988234196106651245061149 56620587823539994216897931)
        ·
          refine ⟨84930881735309991325346897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56620587823539994216897931 84930881735309991325346897)
          ·
            refine ⟨63698161301482493494010173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84930881735309991325346897 63698161301482493494010173)
            ·
              refine ⟨23886810488055935060253815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63698161301482493494010173 23886810488055935060253815)
              ·
                refine ⟨35830215732083902590380723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23886810488055935060253815 35830215732083902590380723)
                ·
                  refine ⟨53745323598125853885571085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35830215732083902590380723 53745323598125853885571085)
                  ·
                    refine ⟨20154496349297195207089157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53745323598125853885571085 20154496349297195207089157)
                    ·
                      refine ⟨3778968065493224101329217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20154496349297195207089157 3778968065493224101329217)
                      ·
                        rfl

theorem cell23_7359514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_7359514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359514 prefixEnd_7359514 := by exact prefixLift 7359514
  have htrace : WordTrace (prefixWord ++ tailWord_7359514) baseStart_7359514 baseEnd_7359514 := by
    simpa [prefixWord, tailWord_7359514, baseEnd_7359514] using wordTrace_append hprefix tailTrace_7359514
  have hstable : (prefixWord ++ tailWord_7359514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359514).length < 2 ^ (prefixWord ++ tailWord_7359514).sum := by decide
  have hdescent : baseEnd_7359514 < baseStart_7359514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359564 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 1, 7, 3]
def baseStart_7359564 : Nat := 118140960795 + 7359564 * 2 ^ 59
def prefixEnd_7359564 : Nat := 4983230072969 + 3 ^ 40 * 7359564 * 2
def baseEnd_7359564 : Nat := 3778993739525948905703987

theorem tailTrace_7359564 : CollatzResearch.WordTrace tailWord_7359564 prefixEnd_7359564 3778993739525948905703987 := by
  unfold tailWord_7359564
  simp only [CollatzResearch.WordTrace]
  refine ⟨134212675554782008154158873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178950234073042677538878497 134212675554782008154158873)
  ·
    refine ⟨100659506666086506115619155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134212675554782008154158873 100659506666086506115619155)
    ·
      refine ⟨150989259999129759173428733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100659506666086506115619155 150989259999129759173428733)
      ·
        refine ⟨56620972499673659690035775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150989259999129759173428733 56620972499673659690035775)
        ·
          refine ⟨84931458749510489535053663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56620972499673659690035775 84931458749510489535053663)
          ·
            refine ⟨127397188124265734302580495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84931458749510489535053663 127397188124265734302580495)
            ·
              refine ⟨191095782186398601453870743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127397188124265734302580495 191095782186398601453870743)
              ·
                refine ⟨286643673279597902180806115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191095782186398601453870743 286643673279597902180806115)
                ·
                  refine ⟨429965509919396853271209173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286643673279597902180806115 429965509919396853271209173)
                  ·
                    refine ⟨10077316638735863748543965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 429965509919396853271209173 10077316638735863748543965)
                    ·
                      refine ⟨3778993739525948905703987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10077316638735863748543965 3778993739525948905703987)
                      ·
                        rfl

theorem cell23_7359564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_7359564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359564 prefixEnd_7359564 := by exact prefixLift 7359564
  have htrace : WordTrace (prefixWord ++ tailWord_7359564) baseStart_7359564 baseEnd_7359564 := by
    simpa [prefixWord, tailWord_7359564, baseEnd_7359564] using wordTrace_append hprefix tailTrace_7359564
  have hstable : (prefixWord ++ tailWord_7359564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359564).length < 2 ^ (prefixWord ++ tailWord_7359564).sum := by decide
  have hdescent : baseEnd_7359564 < baseStart_7359564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359592 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 3, 4]
def baseStart_7359592 : Nat := 118140960795 + 7359592 * 2 ^ 59
def prefixEnd_7359592 : Nat := 4983230072969 + 3 ^ 40 * 7359592 * 2
def baseEnd_7359592 : Nat := 1259669372328091598717953

theorem tailTrace_7359592 : CollatzResearch.WordTrace tailWord_7359592 prefixEnd_7359592 1259669372328091598717953 := by
  unfold tailWord_7359592
  simp only [CollatzResearch.WordTrace]
  refine ⟨134213186176731288545168515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178950914902308384726891353 134213186176731288545168515)
  ·
    refine ⟨201319779265096932817752773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134213186176731288545168515 201319779265096932817752773)
    ·
      refine ⟨37747458612205674903328645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201319779265096932817752773 37747458612205674903328645)
      ·
        refine ⟨7077648489788564044374121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37747458612205674903328645 7077648489788564044374121)
        ·
          refine ⟨5308236367341423033280591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7077648489788564044374121 5308236367341423033280591)
          ·
            refine ⟨7962354551012134549920887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5308236367341423033280591 7962354551012134549920887)
            ·
              refine ⟨11943531826518201824881331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7962354551012134549920887 11943531826518201824881331)
              ·
                refine ⟨17915297739777302737321997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11943531826518201824881331 17915297739777302737321997)
                ·
                  refine ⟨6718236652416488526495749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17915297739777302737321997 6718236652416488526495749)
                  ·
                    refine ⟨1259669372328091598717953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6718236652416488526495749 1259669372328091598717953)
                    ·
                      rfl

theorem cell23_7359592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_7359592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359592 prefixEnd_7359592 := by exact prefixLift 7359592
  have htrace : WordTrace (prefixWord ++ tailWord_7359592) baseStart_7359592 baseEnd_7359592 := by
    simpa [prefixWord, tailWord_7359592, baseEnd_7359592] using wordTrace_append hprefix tailTrace_7359592
  have hstable : (prefixWord ++ tailWord_7359592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359592).length < 2 ^ (prefixWord ++ tailWord_7359592).sum := by decide
  have hdescent : baseEnd_7359592 < baseStart_7359592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359644 : List Nat := [2, 2, 3, 2, 1, 13]
def baseStart_7359644 : Nat := 118140960795 + 7359644 * 2 ^ 59
def prefixEnd_7359644 : Nat := 4983230072969 + 3 ^ 40 * 7359644 * 2
def baseEnd_7359644 : Nat := 15551583613079459229233

theorem tailTrace_7359644 : CollatzResearch.WordTrace tailWord_7359644 prefixEnd_7359644 15551583613079459229233 := by
  unfold tailWord_7359644
  simp only [CollatzResearch.WordTrace]
  refine ⟨134214134474637094985614993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178952179299516126647486657 134214134474637094985614993)
  ·
    refine ⟨100660600855977821239211245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134214134474637094985614993 100660600855977821239211245)
    ·
      refine ⟨37747725320991682964704217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100660600855977821239211245 37747725320991682964704217)
      ·
        refine ⟨28310793990743762223528163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37747725320991682964704217 28310793990743762223528163)
        ·
          refine ⟨42466190986115643335292245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28310793990743762223528163 42466190986115643335292245)
          ·
            refine ⟨15551583613079459229233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 42466190986115643335292245 15551583613079459229233)
            ·
              rfl

theorem cell23_7359644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 13].length) (baseStart_7359644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359644 prefixEnd_7359644 := by exact prefixLift 7359644
  have htrace : WordTrace (prefixWord ++ tailWord_7359644) baseStart_7359644 baseEnd_7359644 := by
    simpa [prefixWord, tailWord_7359644, baseEnd_7359644] using wordTrace_append hprefix tailTrace_7359644
  have hstable : (prefixWord ++ tailWord_7359644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359644).length < 2 ^ (prefixWord ++ tailWord_7359644).sum := by decide
  have hdescent : baseEnd_7359644 < baseStart_7359644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359648 : List Nat := [2, 1, 1, 4, 2, 1, 4, 2, 2, 4]
def baseStart_7359648 : Nat := 118140960795 + 7359648 * 2 ^ 59
def prefixEnd_7359648 : Nat := 4983230072969 + 3 ^ 40 * 7359648 * 2
def baseEnd_7359648 : Nat := 1259678957300308859017867

theorem tailTrace_7359648 : CollatzResearch.WordTrace tailWord_7359648 prefixEnd_7359648 1259678957300308859017867 := by
  unfold tailWord_7359648
  simp only [CollatzResearch.WordTrace]
  refine ⟨134214207420629849327187799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178952276560839799102917065 134214207420629849327187799)
  ·
    refine ⟨201321311130944773990781699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134214207420629849327187799 201321311130944773990781699)
    ·
      refine ⟨301981966696417160986172549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201321311130944773990781699 301981966696417160986172549)
      ·
        refine ⟨56621618755578217684907353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301981966696417160986172549 56621618755578217684907353)
        ·
          refine ⟨42466214066683663263680515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56621618755578217684907353 42466214066683663263680515)
          ·
            refine ⟨63699321100025494895520773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42466214066683663263680515 63699321100025494895520773)
            ·
              refine ⟨11943622706254780292910145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63699321100025494895520773 11943622706254780292910145)
              ·
                refine ⟨8957717029691085219682609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11943622706254780292910145 8957717029691085219682609)
                ·
                  refine ⟨6718287772268313914761957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8957717029691085219682609 6718287772268313914761957)
                  ·
                    refine ⟨1259678957300308859017867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6718287772268313914761957 1259678957300308859017867)
                    ·
                      rfl

theorem cell23_7359648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 2, 4].length) (baseStart_7359648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359648 prefixEnd_7359648 := by exact prefixLift 7359648
  have htrace : WordTrace (prefixWord ++ tailWord_7359648) baseStart_7359648 baseEnd_7359648 := by
    simpa [prefixWord, tailWord_7359648, baseEnd_7359648] using wordTrace_append hprefix tailTrace_7359648
  have hstable : (prefixWord ++ tailWord_7359648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359648).length < 2 ^ (prefixWord ++ tailWord_7359648).sum := by decide
  have hdescent : baseEnd_7359648 < baseStart_7359648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359674 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 4, 7]
def baseStart_7359674 : Nat := 118140960795 + 7359674 * 2 ^ 59
def prefixEnd_7359674 : Nat := 4983230072969 + 3 ^ 40 * 7359674 * 2
def baseEnd_7359674 : Nat := 1259683407465981158442827

theorem tailTrace_7359674 : CollatzResearch.WordTrace tailWord_7359674 prefixEnd_7359674 1259683407465981158442827 := by
  unfold tailWord_7359674
  simp only [CollatzResearch.WordTrace]
  refine ⟨67107340784791376273705519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178952908759443670063214717 67107340784791376273705519)
  ·
    refine ⟨100661011177187064410558279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67107340784791376273705519 100661011177187064410558279)
    ·
      refine ⟨150991516765780596615837419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100661011177187064410558279 150991516765780596615837419)
      ·
        refine ⟨226487275148670894923756129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150991516765780596615837419 226487275148670894923756129)
        ·
          refine ⟨169865456361503171192817097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226487275148670894923756129 169865456361503171192817097)
          ·
            refine ⟨127399092271127378394612823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169865456361503171192817097 127399092271127378394612823)
            ·
              refine ⟨191098638406691067591919235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127399092271127378394612823 191098638406691067591919235)
              ·
                refine ⟨286647957610036601387878853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191098638406691067591919235 286647957610036601387878853)
                ·
                  refine ⟨53746492051881862760227285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286647957610036601387878853 53746492051881862760227285)
                  ·
                    refine ⟨1259683407465981158442827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53746492051881862760227285 1259683407465981158442827)
                    ·
                      rfl

theorem cell23_7359674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_7359674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359674 prefixEnd_7359674 := by exact prefixLift 7359674
  have htrace : WordTrace (prefixWord ++ tailWord_7359674) baseStart_7359674 baseEnd_7359674 := by
    simpa [prefixWord, tailWord_7359674, baseEnd_7359674] using wordTrace_append hprefix tailTrace_7359674
  have hstable : (prefixWord ++ tailWord_7359674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359674).length < 2 ^ (prefixWord ++ tailWord_7359674).sum := by decide
  have hdescent : baseEnd_7359674 < baseStart_7359674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359678 : List Nat := [4, 2, 1, 1, 3, 2, 3, 7]
def baseStart_7359678 : Nat := 118140960795 + 7359678 * 2 ^ 59
def prefixEnd_7359678 : Nat := 4983230072969 + 3 ^ 40 * 7359678 * 2
def baseEnd_7359678 : Nat := 139964899122983757765869

theorem tailTrace_7359678 : CollatzResearch.WordTrace tailWord_7359678 prefixEnd_7359678 139964899122983757765869 := by
  unfold tailWord_7359678
  simp only [CollatzResearch.WordTrace]
  refine ⟨33553688628893876722245961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178953006020767342518645125 33553688628893876722245961)
  ·
    refine ⟨25165266471670407541684471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33553688628893876722245961 25165266471670407541684471)
    ·
      refine ⟨37747899707505611312526707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25165266471670407541684471 37747899707505611312526707)
      ·
        refine ⟨56621849561258416968790061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37747899707505611312526707 56621849561258416968790061)
        ·
          refine ⟨21233193585471906363296273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56621849561258416968790061 21233193585471906363296273)
          ·
            refine ⟨15924895189103929772472205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21233193585471906363296273 15924895189103929772472205)
            ·
              refine ⟨5971835695913973664677077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15924895189103929772472205 5971835695913973664677077)
              ·
                refine ⟨139964899122983757765869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5971835695913973664677077 139964899122983757765869)
                ·
                  rfl

theorem cell23_7359678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_7359678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359678 prefixEnd_7359678 := by exact prefixLift 7359678
  have htrace : WordTrace (prefixWord ++ tailWord_7359678) baseStart_7359678 baseEnd_7359678 := by
    simpa [prefixWord, tailWord_7359678, baseEnd_7359678] using wordTrace_append hprefix tailTrace_7359678
  have hstable : (prefixWord ++ tailWord_7359678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359678).length < 2 ^ (prefixWord ++ tailWord_7359678).sum := by decide
  have hdescent : baseEnd_7359678 < baseStart_7359678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359686 : List Nat := [6, 1, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_7359686 : Nat := 118140960795 + 7359686 * 2 ^ 59
def prefixEnd_7359686 : Nat := 4983230072969 + 3 ^ 40 * 7359686 * 2
def baseEnd_7359686 : Nat := 1259685461388599142792809

theorem tailTrace_7359686 : CollatzResearch.WordTrace tailWord_7359686 prefixEnd_7359686 1259685461388599142792809 := by
  unfold tailWord_7359686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8388431275472563473258091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178953200543414687429505941 8388431275472563473258091)
  ·
    refine ⟨12582646913208845209887137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8388431275472563473258091 12582646913208845209887137)
    ·
      refine ⟨9436985184906633907415353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12582646913208845209887137 9436985184906633907415353)
      ·
        refine ⟨7077738888679975430561515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9436985184906633907415353 7077738888679975430561515)
        ·
          refine ⟨10616608333019963145842273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7077738888679975430561515 10616608333019963145842273)
          ·
            refine ⟨7962456249764972359381705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10616608333019963145842273 7962456249764972359381705)
            ·
              refine ⟨5971842187323729269536279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7962456249764972359381705 5971842187323729269536279)
              ·
                refine ⟨8957763280985593904304419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5971842187323729269536279 8957763280985593904304419)
                ·
                  refine ⟨13436644921478390856456629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8957763280985593904304419 13436644921478390856456629)
                  ·
                    refine ⟨1259685461388599142792809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13436644921478390856456629 1259685461388599142792809)
                    ·
                      rfl

theorem cell23_7359686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_7359686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359686 prefixEnd_7359686 := by exact prefixLift 7359686
  have htrace : WordTrace (prefixWord ++ tailWord_7359686) baseStart_7359686 baseEnd_7359686 := by
    simpa [prefixWord, tailWord_7359686, baseEnd_7359686] using wordTrace_append hprefix tailTrace_7359686
  have hstable : (prefixWord ++ tailWord_7359686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359686).length < 2 ^ (prefixWord ++ tailWord_7359686).sum := by decide
  have hdescent : baseEnd_7359686 < baseStart_7359686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359722 : List Nat := [3, 1, 3, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_7359722 : Nat := 118140960795 + 7359722 * 2 ^ 59
def prefixEnd_7359722 : Nat := 4983230072969 + 3 ^ 40 * 7359722 * 2
def baseEnd_7359722 : Nat := 3779074869469359287528261

theorem tailTrace_7359722 : CollatzResearch.WordTrace tailWord_7359722 prefixEnd_7359722 3779074869469359287528261 := by
  unfold tailWord_7359722
  simp only [CollatzResearch.WordTrace]
  refine ⟨67107778460747902323142355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178954075895327739528379613 67107778460747902323142355)
  ·
    refine ⟨100661667691121853484713533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67107778460747902323142355 100661667691121853484713533)
    ·
      refine ⟨37748125384170695056767575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100661667691121853484713533 37748125384170695056767575)
      ·
        refine ⟨56622188076256042585151363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37748125384170695056767575 56622188076256042585151363)
        ·
          refine ⟨84933282114384063877727045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56622188076256042585151363 84933282114384063877727045)
          ·
            refine ⟨15924990396447011977073821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84933282114384063877727045 15924990396447011977073821)
            ·
              refine ⟨5971871398667629491402683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15924990396447011977073821 5971871398667629491402683)
              ·
                refine ⟨8957807098001444237104025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5971871398667629491402683 8957807098001444237104025)
                ·
                  refine ⟨6718355323501083177828019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8957807098001444237104025 6718355323501083177828019)
                  ·
                    refine ⟨10077532985251624766742029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6718355323501083177828019 10077532985251624766742029)
                    ·
                      refine ⟨3779074869469359287528261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10077532985251624766742029 3779074869469359287528261)
                      ·
                        rfl

theorem cell23_7359722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_7359722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359722 prefixEnd_7359722 := by exact prefixLift 7359722
  have htrace : WordTrace (prefixWord ++ tailWord_7359722) baseStart_7359722 baseEnd_7359722 := by
    simpa [prefixWord, tailWord_7359722, baseEnd_7359722] using wordTrace_append hprefix tailTrace_7359722
  have hstable : (prefixWord ++ tailWord_7359722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359722).length < 2 ^ (prefixWord ++ tailWord_7359722).sum := by decide
  have hdescent : baseEnd_7359722 < baseStart_7359722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359745 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_7359745 : Nat := 118140960795 + 7359745 * 2 ^ 59
def prefixEnd_7359745 : Nat := 4983230072969 + 3 ^ 40 * 7359745 * 2
def baseEnd_7359745 : Nat := 3779086679524412697540655

theorem tailTrace_7359745 : CollatzResearch.WordTrace tailWord_7359745 prefixEnd_7359745 3779086679524412697540655 := by
  unfold tailWord_7359745
  simp only [CollatzResearch.WordTrace]
  refine ⟨268431952721908284220656689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178954635147938856147104459 268431952721908284220656689)
  ·
    refine ⟨201323964541431213165492517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268431952721908284220656689 201323964541431213165492517)
    ·
      refine ⟨37748243351518352468529847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201323964541431213165492517 37748243351518352468529847)
      ·
        refine ⟨56622365027277528702794771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37748243351518352468529847 56622365027277528702794771)
        ·
          refine ⟨84933547540916293054192157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56622365027277528702794771 84933547540916293054192157)
          ·
            refine ⟨31850080327843609895322059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84933547540916293054192157 31850080327843609895322059)
            ·
              refine ⟨47775120491765414842983089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31850080327843609895322059 47775120491765414842983089)
              ·
                refine ⟨35831340368824061132237317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47775120491765414842983089 35831340368824061132237317)
                ·
                  refine ⟨6718376319154511462294497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35831340368824061132237317 6718376319154511462294497)
                  ·
                    refine ⟨5038782239365883596720873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6718376319154511462294497 5038782239365883596720873)
                    ·
                      refine ⟨3779086679524412697540655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5038782239365883596720873 3779086679524412697540655)
                      ·
                        rfl

theorem cell23_7359745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_7359745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359745 prefixEnd_7359745 := by exact prefixLift 7359745
  have htrace : WordTrace (prefixWord ++ tailWord_7359745) baseStart_7359745 baseEnd_7359745 := by
    simpa [prefixWord, tailWord_7359745, baseEnd_7359745] using wordTrace_append hprefix tailTrace_7359745
  have hstable : (prefixWord ++ tailWord_7359745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359745).length < 2 ^ (prefixWord ++ tailWord_7359745).sum := by decide
  have hdescent : baseEnd_7359745 < baseStart_7359745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359748 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_7359748 : Nat := 118140960795 + 7359748 * 2 ^ 59
def prefixEnd_7359748 : Nat := 4983230072969 + 3 ^ 40 * 7359748 * 2
def baseEnd_7359748 : Nat := 3779088219966376185803141

theorem tailTrace_7359748 : CollatzResearch.WordTrace tailWord_7359748 prefixEnd_7359748 3779088219966376185803141 := by
  unfold tailWord_7359748
  simp only [CollatzResearch.WordTrace]
  refine ⟨134216031070448707866507949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178954708093931610488677265 134216031070448707866507949)
  ·
    refine ⟨50331011651418265449940481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134216031070448707866507949 50331011651418265449940481)
    ·
      refine ⟨37748258738563699087455361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50331011651418265449940481 37748258738563699087455361)
      ·
        refine ⟨28311194053922774315591521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37748258738563699087455361 28311194053922774315591521)
        ·
          refine ⟨21233395540442080736693641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28311194053922774315591521 21233395540442080736693641)
          ·
            refine ⟨15925046655331560552520231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21233395540442080736693641 15925046655331560552520231)
            ·
              refine ⟨23887569982997340828780347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15925046655331560552520231 23887569982997340828780347)
              ·
                refine ⟨35831354974496011243170521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23887569982997340828780347 35831354974496011243170521)
                ·
                  refine ⟨26873516230872008432377891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35831354974496011243170521 26873516230872008432377891)
                  ·
                    refine ⟨40310274346308012648566837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26873516230872008432377891 40310274346308012648566837)
                    ·
                      refine ⟨3779088219966376185803141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40310274346308012648566837 3779088219966376185803141)
                      ·
                        rfl

theorem cell23_7359748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_7359748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359748 prefixEnd_7359748 := by exact prefixLift 7359748
  have htrace : WordTrace (prefixWord ++ tailWord_7359748) baseStart_7359748 baseEnd_7359748 := by
    simpa [prefixWord, tailWord_7359748, baseEnd_7359748] using wordTrace_append hprefix tailTrace_7359748
  have hstable : (prefixWord ++ tailWord_7359748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359748).length < 2 ^ (prefixWord ++ tailWord_7359748).sum := by decide
  have hdescent : baseEnd_7359748 < baseStart_7359748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359768 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 7]
def baseStart_7359768 : Nat := 118140960795 + 7359768 * 2 ^ 59
def prefixEnd_7359768 : Nat := 4983230072969 + 3 ^ 40 * 7359768 * 2
def baseEnd_7359768 : Nat := 419899832175496234172561

theorem tailTrace_7359768 : CollatzResearch.WordTrace tailWord_7359768 prefixEnd_7359768 419899832175496234172561 := by
  unfold tailWord_7359768
  simp only [CollatzResearch.WordTrace]
  refine ⟨134216395800412479574371979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178955194400549972765829305 134216395800412479574371979)
  ·
    refine ⟨201324593700618719361557969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134216395800412479574371979 201324593700618719361557969)
    ·
      refine ⟨150993445275464039521168477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201324593700618719361557969 150993445275464039521168477)
      ·
        refine ⟨56622541978299014820438179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150993445275464039521168477 56622541978299014820438179)
        ·
          refine ⟨84933812967448522230657269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56622541978299014820438179 84933812967448522230657269)
          ·
            refine ⟨7962544965698298959124119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84933812967448522230657269 7962544965698298959124119)
            ·
              refine ⟨11943817448547448438686179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7962544965698298959124119 11943817448547448438686179)
              ·
                refine ⟨17915726172821172658029269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11943817448547448438686179 17915726172821172658029269)
                ·
                  refine ⟨419899832175496234172561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17915726172821172658029269 419899832175496234172561)
                  ·
                    rfl

theorem cell23_7359768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 7].length) (baseStart_7359768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359768 prefixEnd_7359768 := by exact prefixLift 7359768
  have htrace : WordTrace (prefixWord ++ tailWord_7359768) baseStart_7359768 baseEnd_7359768 := by
    simpa [prefixWord, tailWord_7359768, baseEnd_7359768] using wordTrace_append hprefix tailTrace_7359768
  have hstable : (prefixWord ++ tailWord_7359768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359768).length < 2 ^ (prefixWord ++ tailWord_7359768).sum := by decide
  have hdescent : baseEnd_7359768 < baseStart_7359768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359779 : List Nat := [1, 1, 1, 4, 2, 5, 2, 1, 2, 2, 2]
def baseStart_7359779 : Nat := 118140960795 + 7359779 * 2 ^ 59
def prefixEnd_7359779 : Nat := 4983230072969 + 3 ^ 40 * 7359779 * 2
def baseEnd_7359779 : Nat := 3779104137866665564515499

theorem tailTrace_7359779 : CollatzResearch.WordTrace tailWord_7359779 prefixEnd_7359779 3779104137866665564515499 := by
  unfold tailWord_7359779
  simp only [CollatzResearch.WordTrace]
  refine ⟨268433192803785108027394391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178955461869190072018262927 268433192803785108027394391)
  ·
    refine ⟨402649789205677662041091587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268433192803785108027394391 402649789205677662041091587)
    ·
      refine ⟨603974683808516493061637381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402649789205677662041091587 603974683808516493061637381)
      ·
        refine ⟨113245253214096842449057009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 603974683808516493061637381 113245253214096842449057009)
        ·
          refine ⟨84933939910572631836792757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113245253214096842449057009 84933939910572631836792757)
          ·
            refine ⟨7962556866616184234699321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84933939910572631836792757 7962556866616184234699321)
            ·
              refine ⟨5971917649962138176024491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7962556866616184234699321 5971917649962138176024491)
              ·
                refine ⟨8957876474943207264036737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5971917649962138176024491 8957876474943207264036737)
                ·
                  refine ⟨6718407356207405448027553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8957876474943207264036737 6718407356207405448027553)
                  ·
                    refine ⟨5038805517155554086020665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6718407356207405448027553 5038805517155554086020665)
                    ·
                      refine ⟨3779104137866665564515499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5038805517155554086020665 3779104137866665564515499)
                      ·
                        rfl

theorem cell23_7359779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_7359779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359779 prefixEnd_7359779 := by exact prefixLift 7359779
  have htrace : WordTrace (prefixWord ++ tailWord_7359779) baseStart_7359779 baseEnd_7359779 := by
    simpa [prefixWord, tailWord_7359779, baseEnd_7359779] using wordTrace_append hprefix tailTrace_7359779
  have hstable : (prefixWord ++ tailWord_7359779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359779).length < 2 ^ (prefixWord ++ tailWord_7359779).sum := by decide
  have hdescent : baseEnd_7359779 < baseStart_7359779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359818 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 3, 6, 2]
def baseStart_7359818 : Nat := 118140960795 + 7359818 * 2 ^ 59
def prefixEnd_7359818 : Nat := 4983230072969 + 3 ^ 40 * 7359818 * 2
def baseEnd_7359818 : Nat := 3779124163612190911927819

theorem tailTrace_7359818 : CollatzResearch.WordTrace tailWord_7359818 prefixEnd_7359818 3779124163612190911927819 := by
  unfold tailWord_7359818
  simp only [CollatzResearch.WordTrace]
  refine ⟨67108653812660954422016027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178956410167095878458709405 67108653812660954422016027)
  ·
    refine ⟨100662980718991431633024041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67108653812660954422016027 100662980718991431633024041)
    ·
      refine ⟨75497235539243573724768031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100662980718991431633024041 75497235539243573724768031)
      ·
        refine ⟨113245853308865360587152047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75497235539243573724768031 113245853308865360587152047)
        ·
          refine ⟨169868779963298040880728071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113245853308865360587152047 169868779963298040880728071)
          ·
            refine ⟨254803169944947061321092107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169868779963298040880728071 254803169944947061321092107)
            ·
              refine ⟨382204754917420591981638161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254803169944947061321092107 382204754917420591981638161)
              ·
                refine ⟨286653566188065443986228621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382204754917420591981638161 286653566188065443986228621)
                ·
                  refine ⟨107495087320524541494835733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286653566188065443986228621 107495087320524541494835733)
                  ·
                    refine ⟨5038832218149587882570425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107495087320524541494835733 5038832218149587882570425)
                    ·
                      refine ⟨3779124163612190911927819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5038832218149587882570425 3779124163612190911927819)
                      ·
                        rfl

theorem cell23_7359818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_7359818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359818 prefixEnd_7359818 := by exact prefixLift 7359818
  have htrace : WordTrace (prefixWord ++ tailWord_7359818) baseStart_7359818 baseEnd_7359818 := by
    simpa [prefixWord, tailWord_7359818, baseEnd_7359818] using wordTrace_append hprefix tailTrace_7359818
  have hstable : (prefixWord ++ tailWord_7359818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359818).length < 2 ^ (prefixWord ++ tailWord_7359818).sum := by decide
  have hdescent : baseEnd_7359818 < baseStart_7359818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359875 : List Nat := [1, 1, 1, 3, 5, 3, 1, 2, 6]
def baseStart_7359875 : Nat := 118140960795 + 7359875 * 2 ^ 59
def prefixEnd_7359875 : Nat := 4983230072969 + 3 ^ 40 * 7359875 * 2
def baseEnd_7359875 : Nat := 419905936889944132101673

theorem tailTrace_7359875 : CollatzResearch.WordTrace tailWord_7359875 prefixEnd_7359875 419905936889944132101673 := by
  unfold tailWord_7359875
  simp only [CollatzResearch.WordTrace]
  refine ⟨268436694211437316422889079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178957796140958210948592719 268436694211437316422889079)
  ·
    refine ⟨402655041317155974634333619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268436694211437316422889079 402655041317155974634333619)
    ·
      refine ⟨603982561975733961951500429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402655041317155974634333619 603982561975733961951500429)
      ·
        refine ⟨226493460740900235731812661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 603982561975733961951500429 226493460740900235731812661)
        ·
          refine ⟨21233761944459397099857437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226493460740900235731812661 21233761944459397099857437)
          ·
            refine ⟨7962660729172273912446539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21233761944459397099857437 7962660729172273912446539)
            ·
              refine ⟨11943991093758410868669809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7962660729172273912446539 11943991093758410868669809)
              ·
                refine ⟨8957993320318808151502357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11943991093758410868669809 8957993320318808151502357)
                ·
                  refine ⟨419905936889944132101673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8957993320318808151502357 419905936889944132101673)
                  ·
                    rfl

theorem cell23_7359875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 6].length) (baseStart_7359875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359875 prefixEnd_7359875 := by exact prefixLift 7359875
  have htrace : WordTrace (prefixWord ++ tailWord_7359875) baseStart_7359875 baseEnd_7359875 := by
    simpa [prefixWord, tailWord_7359875, baseEnd_7359875] using wordTrace_append hprefix tailTrace_7359875
  have hstable : (prefixWord ++ tailWord_7359875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359875).length < 2 ^ (prefixWord ++ tailWord_7359875).sum := by decide
  have hdescent : baseEnd_7359875 < baseStart_7359875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359892 : List Nat := [2, 4, 2, 1, 2, 2, 3, 1, 6]
def baseStart_7359892 : Nat := 118140960795 + 7359892 * 2 ^ 59
def prefixEnd_7359892 : Nat := 4983230072969 + 3 ^ 40 * 7359892 * 2
def baseEnd_7359892 : Nat := 419906906797847069155831

theorem tailTrace_7359892 : CollatzResearch.WordTrace tailWord_7359892 prefixEnd_7359892 419906906797847069155831 := by
  unfold tailWord_7359892
  simp only [CollatzResearch.WordTrace]
  refine ⟨134218657126187864163128965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178958209501583818884171953 134218657126187864163128965)
  ·
    refine ⟨25165998211160224530586681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134218657126187864163128965 25165998211160224530586681)
    ·
      refine ⟨18874498658370168397940011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25165998211160224530586681 18874498658370168397940011)
      ·
        refine ⟨28311747987555252596910017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18874498658370168397940011 28311747987555252596910017)
        ·
          refine ⟨21233810990666439447682513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28311747987555252596910017 21233810990666439447682513)
          ·
            refine ⟨15925358242999829585761885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21233810990666439447682513 15925358242999829585761885)
            ·
              refine ⟨5972009341124936094660707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15925358242999829585761885 5972009341124936094660707)
              ·
                refine ⟨8958014011687404141991061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5972009341124936094660707 8958014011687404141991061)
                ·
                  refine ⟨419906906797847069155831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8958014011687404141991061 419906906797847069155831)
                  ·
                    rfl

theorem cell23_7359892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_7359892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359892 prefixEnd_7359892 := by exact prefixLift 7359892
  have htrace : WordTrace (prefixWord ++ tailWord_7359892) baseStart_7359892 baseEnd_7359892 := by
    simpa [prefixWord, tailWord_7359892, baseEnd_7359892] using wordTrace_append hprefix tailTrace_7359892
  have hstable : (prefixWord ++ tailWord_7359892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359892).length < 2 ^ (prefixWord ++ tailWord_7359892).sum := by decide
  have hdescent : baseEnd_7359892 < baseStart_7359892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359928 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 1, 1, 5]
def baseStart_7359928 : Nat := 118140960795 + 7359928 * 2 ^ 59
def prefixEnd_7359928 : Nat := 4983230072969 + 3 ^ 40 * 7359928 * 2
def baseEnd_7359928 : Nat := 3779180646484185481552313

theorem tailTrace_7359928 : CollatzResearch.WordTrace tailWord_7359928 prefixEnd_7359928 3779180646484185481552313 := by
  unfold tailWord_7359928
  simp only [CollatzResearch.WordTrace]
  refine ⟨134219313640122653237284219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178959084853496870983045625 134219313640122653237284219)
  ·
    refine ⟨201328970460183979855926329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134219313640122653237284219 201328970460183979855926329)
    ·
      refine ⟨150996727845137984891944747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201328970460183979855926329 150996727845137984891944747)
      ·
        refine ⟨226495091767706977337917121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150996727845137984891944747 226495091767706977337917121)
        ·
          refine ⟨169871318825780233003437841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226495091767706977337917121 169871318825780233003437841)
          ·
            refine ⟨127403489119335174752578381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169871318825780233003437841 127403489119335174752578381)
            ·
              refine ⟨47776308419750690532216893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127403489119335174752578381 47776308419750690532216893)
              ·
                refine ⟨17916115657406508949581335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47776308419750690532216893 17916115657406508949581335)
                ·
                  refine ⟨26874173486109763424372003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17916115657406508949581335 26874173486109763424372003)
                  ·
                    refine ⟨40311260229164645136558005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26874173486109763424372003 40311260229164645136558005)
                    ·
                      refine ⟨3779180646484185481552313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40311260229164645136558005 3779180646484185481552313)
                      ·
                        rfl

theorem cell23_7359928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_7359928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359928 prefixEnd_7359928 := by exact prefixLift 7359928
  have htrace : WordTrace (prefixWord ++ tailWord_7359928) baseStart_7359928 baseEnd_7359928 := by
    simpa [prefixWord, tailWord_7359928, baseEnd_7359928] using wordTrace_append hprefix tailTrace_7359928
  have hstable : (prefixWord ++ tailWord_7359928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359928).length < 2 ^ (prefixWord ++ tailWord_7359928).sum := by decide
  have hdescent : baseEnd_7359928 < baseStart_7359928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359948 : List Nat := [2, 2, 1, 4, 2, 1, 1, 10]
def baseStart_7359948 : Nat := 118140960795 + 7359948 * 2 ^ 59
def prefixEnd_7359948 : Nat := 4983230072969 + 3 ^ 40 * 7359948 * 2
def baseEnd_7359948 : Nat := 139970033929528718640823

theorem tailTrace_7359948 : CollatzResearch.WordTrace tailWord_7359948 prefixEnd_7359948 139970033929528718640823 := by
  unfold tailWord_7359948
  simp only [CollatzResearch.WordTrace]
  refine ⟨134219678370086424945148249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178959571160115233260197665 134219678370086424945148249)
  ·
    refine ⟨100664758777564818708861187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134219678370086424945148249 100664758777564818708861187)
    ·
      refine ⟨150997138166347228063291781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100664758777564818708861187 150997138166347228063291781)
      ·
        refine ⟨28311963406190105261867209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150997138166347228063291781 28311963406190105261867209)
        ·
          refine ⟨21233972554642578946400407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28311963406190105261867209 21233972554642578946400407)
          ·
            refine ⟨31850958831963868419600611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21233972554642578946400407 31850958831963868419600611)
            ·
              refine ⟨47776438247945802629400917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31850958831963868419600611 47776438247945802629400917)
              ·
                refine ⟨139970033929528718640823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47776438247945802629400917 139970033929528718640823)
                ·
                  rfl

theorem cell23_7359948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 10].length) (baseStart_7359948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359948 prefixEnd_7359948 := by exact prefixLift 7359948
  have htrace : WordTrace (prefixWord ++ tailWord_7359948) baseStart_7359948 baseEnd_7359948 := by
    simpa [prefixWord, tailWord_7359948, baseEnd_7359948] using wordTrace_append hprefix tailTrace_7359948
  have hstable : (prefixWord ++ tailWord_7359948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359948).length < 2 ^ (prefixWord ++ tailWord_7359948).sum := by decide
  have hdescent : baseEnd_7359948 < baseStart_7359948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359962 : List Nat := [3, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3]
def baseStart_7359962 : Nat := 118140960795 + 7359962 * 2 ^ 59
def prefixEnd_7359962 : Nat := 4983230072969 + 3 ^ 40 * 7359962 * 2
def baseEnd_7359962 : Nat := 3779198104826438348527157

theorem tailTrace_7359962 : CollatzResearch.WordTrace tailWord_7359962 prefixEnd_7359962 3779198104826438348527157 := by
  unfold tailWord_7359962
  simp only [CollatzResearch.WordTrace]
  refine ⟨67109966840530532570326535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178959911574748086854204093 67109966840530532570326535)
  ·
    refine ⟨100664950260795798855489803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67109966840530532570326535 100664950260795798855489803)
    ·
      refine ⟨150997425391193698283234705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100664950260795798855489803 150997425391193698283234705)
      ·
        refine ⟨113248069043395273712426029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150997425391193698283234705 113248069043395273712426029)
        ·
          refine ⟨42468025891273227642159761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113248069043395273712426029 42468025891273227642159761)
          ·
            refine ⟨31851019418454920731619821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42468025891273227642159761 31851019418454920731619821)
            ·
              refine ⟨11944132281920595274357433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31851019418454920731619821 11944132281920595274357433)
              ·
                refine ⟨8958099211440446455768075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11944132281920595274357433 8958099211440446455768075)
                ·
                  refine ⟨13437148817160669683652113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8958099211440446455768075 13437148817160669683652113)
                  ·
                    refine ⟨10077861612870502262739085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13437148817160669683652113 10077861612870502262739085)
                    ·
                      refine ⟨3779198104826438348527157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10077861612870502262739085 3779198104826438348527157)
                      ·
                        rfl

theorem cell23_7359962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_7359962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359962 prefixEnd_7359962 := by exact prefixLift 7359962
  have htrace : WordTrace (prefixWord ++ tailWord_7359962) baseStart_7359962 baseEnd_7359962 := by
    simpa [prefixWord, tailWord_7359962, baseEnd_7359962] using wordTrace_append hprefix tailTrace_7359962
  have hstable : (prefixWord ++ tailWord_7359962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359962).length < 2 ^ (prefixWord ++ tailWord_7359962).sum := by decide
  have hdescent : baseEnd_7359962 < baseStart_7359962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359975 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_7359975 : Nat := 118140960795 + 7359975 * 2 ^ 59
def prefixEnd_7359975 : Nat := 4983230072969 + 3 ^ 40 * 7359975 * 2
def baseEnd_7359975 : Nat := 3779204780074946797664597

theorem tailTrace_7359975 : CollatzResearch.WordTrace tailWord_7359975 prefixEnd_7359975 3779204780074946797664597 := by
  unfold tailWord_7359975
  simp only [CollatzResearch.WordTrace]
  refine ⟨268440341511075033501529379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178960227674050022334352919 268440341511075033501529379)
  ·
    refine ⟨402660512266612550252294069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268440341511075033501529379 402660512266612550252294069)
    ·
      refine ⟨37749423024994926586152569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 402660512266612550252294069 37749423024994926586152569)
      ·
        refine ⟨28312067268746194939614427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37749423024994926586152569 28312067268746194939614427)
        ·
          refine ⟨42468100903119292409421641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28312067268746194939614427 42468100903119292409421641)
          ·
            refine ⟨31851075677339469307066231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42468100903119292409421641 31851075677339469307066231)
            ·
              refine ⟨47776613516009203960599347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31851075677339469307066231 47776613516009203960599347)
              ·
                refine ⟨71664920274013805940899021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47776613516009203960599347 71664920274013805940899021)
                ·
                  refine ⟨26874345102755177227837133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71664920274013805940899021 26874345102755177227837133)
                  ·
                    refine ⟨10077879413533191460438925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26874345102755177227837133 10077879413533191460438925)
                    ·
                      refine ⟨3779204780074946797664597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10077879413533191460438925 3779204780074946797664597)
                      ·
                        rfl

theorem cell23_7359975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_7359975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359975 prefixEnd_7359975 := by exact prefixLift 7359975
  have htrace : WordTrace (prefixWord ++ tailWord_7359975) baseStart_7359975 baseEnd_7359975 := by
    simpa [prefixWord, tailWord_7359975, baseEnd_7359975] using wordTrace_append hprefix tailTrace_7359975
  have hstable : (prefixWord ++ tailWord_7359975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359975).length < 2 ^ (prefixWord ++ tailWord_7359975).sum := by decide
  have hdescent : baseEnd_7359975 < baseStart_7359975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7359992 : List Nat := [2, 1, 2, 1, 1, 5, 1, 4, 2, 1, 3]
def baseStart_7359992 : Nat := 118140960795 + 7359992 * 2 ^ 59
def prefixEnd_7359992 : Nat := 4983230072969 + 3 ^ 40 * 7359992 * 2
def baseEnd_7359992 : Nat := 3779213509246073231152019

theorem tailTrace_7359992 : CollatzResearch.WordTrace tailWord_7359992 prefixEnd_7359992 3779213509246073231152019 := by
  unfold tailWord_7359992
  simp only [CollatzResearch.WordTrace]
  refine ⟨134220480776006722702449115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178960641034675630269932153 134220480776006722702449115)
  ·
    refine ⟨201330721164010084053673673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134220480776006722702449115 201330721164010084053673673)
    ·
      refine ⟨150998040873007563040255255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201330721164010084053673673 150998040873007563040255255)
      ·
        refine ⟨226497061309511344560382883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150998040873007563040255255 226497061309511344560382883)
        ·
          refine ⟨339745591964267016840574325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226497061309511344560382883 339745591964267016840574325)
          ·
            refine ⟨31851149246650032828803843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 339745591964267016840574325 31851149246650032828803843)
            ·
              refine ⟨47776723869975049243205765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31851149246650032828803843 47776723869975049243205765)
              ·
                refine ⟨8958135725620321733101081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47776723869975049243205765 8958135725620321733101081)
                ·
                  refine ⟨6718601794215241299825811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8958135725620321733101081 6718601794215241299825811)
                  ·
                    refine ⟨10077902691322861949738717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6718601794215241299825811 10077902691322861949738717)
                    ·
                      refine ⟨3779213509246073231152019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10077902691322861949738717 3779213509246073231152019)
                      ·
                        rfl

theorem cell23_7359992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_7359992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7359992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7359992 prefixEnd_7359992 := by exact prefixLift 7359992
  have htrace : WordTrace (prefixWord ++ tailWord_7359992) baseStart_7359992 baseEnd_7359992 := by
    simpa [prefixWord, tailWord_7359992, baseEnd_7359992] using wordTrace_append hprefix tailTrace_7359992
  have hstable : (prefixWord ++ tailWord_7359992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7359992).length < 2 ^ (prefixWord ++ tailWord_7359992).sum := by decide
  have hdescent : baseEnd_7359992 < baseStart_7359992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7359992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360008 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 1, 8]
def baseStart_7360008 : Nat := 118140960795 + 7360008 * 2 ^ 59
def prefixEnd_7360008 : Nat := 4983230072969 + 3 ^ 40 * 7360008 * 2
def baseEnd_7360008 : Nat := 1259740574978848389517315

theorem tailTrace_7360008 : CollatzResearch.WordTrace tailWord_7360008 prefixEnd_7360008 1259740574978848389517315 := by
  unfold tailWord_7360008
  simp only [CollatzResearch.WordTrace]
  refine ⟨134220772559977740068740339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178961030079970320091653785 134220772559977740068740339)
  ·
    refine ⟨201331158839966610103110509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134220772559977740068740339 201331158839966610103110509)
    ·
      refine ⟨75499184564987478788666441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201331158839966610103110509 75499184564987478788666441)
      ·
        refine ⟨56624388423740609091499831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75499184564987478788666441 56624388423740609091499831)
        ·
          refine ⟨84936582635610913637249747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56624388423740609091499831 84936582635610913637249747)
          ·
            refine ⟨127404873953416370455874621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84936582635610913637249747 127404873953416370455874621)
            ·
              refine ⟨47776827732531138920952983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127404873953416370455874621 47776827732531138920952983)
              ·
                refine ⟨71665241598796708381429475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47776827732531138920952983 71665241598796708381429475)
                ·
                  refine ⟨107497862398195062572144213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71665241598796708381429475 107497862398195062572144213)
                  ·
                    refine ⟨1259740574978848389517315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107497862398195062572144213 1259740574978848389517315)
                    ·
                      rfl

theorem cell23_7360008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_7360008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360008 prefixEnd_7360008 := by exact prefixLift 7360008
  have htrace : WordTrace (prefixWord ++ tailWord_7360008) baseStart_7360008 baseEnd_7360008 := by
    simpa [prefixWord, tailWord_7360008, baseEnd_7360008] using wordTrace_append hprefix tailTrace_7360008
  have hstable : (prefixWord ++ tailWord_7360008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360008).length < 2 ^ (prefixWord ++ tailWord_7360008).sum := by decide
  have hdescent : baseEnd_7360008 < baseStart_7360008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360055 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 7]
def baseStart_7360055 : Nat := 118140960795 + 7360055 * 2 ^ 59
def prefixEnd_7360055 : Nat := 4983230072969 + 3 ^ 40 * 7360055 * 2
def baseEnd_7360055 : Nat := 419916206503034053851581

theorem tailTrace_7360055 : CollatzResearch.WordTrace tailWord_7360055 prefixEnd_7360055 419916206503034053851581 := by
  unfold tailWord_7360055
  simp only [CollatzResearch.WordTrace]
  refine ⟨268443259350785207164441619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178962172900523471442961079 268443259350785207164441619)
  ·
    refine ⟨402664889026177810746662429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268443259350785207164441619 402664889026177810746662429)
    ·
      refine ⟨150999333384816679029998411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402664889026177810746662429 150999333384816679029998411)
      ·
        refine ⟨226499000077225018544997617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150999333384816679029998411 226499000077225018544997617)
        ·
          refine ⟨169874250057918763908748213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226499000077225018544997617 169874250057918763908748213)
          ·
            refine ⟨15925710942929884116445145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169874250057918763908748213 15925710942929884116445145)
            ·
              refine ⟨11944283207197413087333859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15925710942929884116445145 11944283207197413087333859)
              ·
                refine ⟨17916424810796119631000789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11944283207197413087333859 17916424810796119631000789)
                ·
                  refine ⟨419916206503034053851581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17916424810796119631000789 419916206503034053851581)
                  ·
                    rfl

theorem cell23_7360055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 7].length) (baseStart_7360055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360055 prefixEnd_7360055 := by exact prefixLift 7360055
  have htrace : WordTrace (prefixWord ++ tailWord_7360055) baseStart_7360055 baseEnd_7360055 := by
    simpa [prefixWord, tailWord_7360055, baseEnd_7360055] using wordTrace_append hprefix tailTrace_7360055
  have hstable : (prefixWord ++ tailWord_7360055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360055).length < 2 ^ (prefixWord ++ tailWord_7360055).sum := by decide
  have hdescent : baseEnd_7360055 < baseStart_7360055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360085 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 2, 5]
def baseStart_7360085 : Nat := 118140960795 + 7360085 * 2 ^ 59
def prefixEnd_7360085 : Nat := 4983230072969 + 3 ^ 40 * 7360085 * 2
def baseEnd_7360085 : Nat := 1259753754315647122429697

theorem tailTrace_7360085 : CollatzResearch.WordTrace tailWord_7360085 prefixEnd_7360085 1259753754315647122429697 := by
  unfold tailWord_7360085
  simp only [CollatzResearch.WordTrace]
  refine ⟨268444353540676522288033709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178962902360451014858689139 268444353540676522288033709)
  ·
    refine ⟨100666632577753695858012641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268444353540676522288033709 100666632577753695858012641)
    ·
      refine ⟨75499974433315271893509481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100666632577753695858012641 75499974433315271893509481)
      ·
        refine ⟨56624980824986453920132111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75499974433315271893509481 56624980824986453920132111)
        ·
          refine ⟨84937471237479680880198167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56624980824986453920132111 84937471237479680880198167)
          ·
            refine ⟨127406206856219521320297251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84937471237479680880198167 127406206856219521320297251)
            ·
              refine ⟨191109310284329281980445877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127406206856219521320297251 191109310284329281980445877)
              ·
                refine ⟨17916497839155870185666801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191109310284329281980445877 17916497839155870185666801)
                ·
                  refine ⟨13437373379366902639250101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17916497839155870185666801 13437373379366902639250101)
                  ·
                    refine ⟨1259753754315647122429697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13437373379366902639250101 1259753754315647122429697)
                    ·
                      rfl

theorem cell23_7360085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_7360085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360085 prefixEnd_7360085 := by exact prefixLift 7360085
  have htrace : WordTrace (prefixWord ++ tailWord_7360085) baseStart_7360085 baseEnd_7360085 := by
    simpa [prefixWord, tailWord_7360085, baseEnd_7360085] using wordTrace_append hprefix tailTrace_7360085
  have hstable : (prefixWord ++ tailWord_7360085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360085).length < 2 ^ (prefixWord ++ tailWord_7360085).sum := by decide
  have hdescent : baseEnd_7360085 < baseStart_7360085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360086 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_7360086 : Nat := 118140960795 + 7360086 * 2 ^ 59
def prefixEnd_7360086 : Nat := 4983230072969 + 3 ^ 40 * 7360086 * 2
def baseEnd_7360086 : Nat := 3779261776427595863376587

theorem tailTrace_7360086 : CollatzResearch.WordTrace tailWord_7360086 prefixEnd_7360086 3779261776427595863376587 := by
  unfold tailWord_7360086
  simp only [CollatzResearch.WordTrace]
  refine ⟨16777774375854556216176257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178962926675781932972546741 16777774375854556216176257)
  ·
    refine ⟨12583330781890917162132193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16777774375854556216176257 12583330781890917162132193)
    ·
      refine ⟨9437498086418187871599145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12583330781890917162132193 9437498086418187871599145)
      ·
        refine ⟨7078123564813640903699359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9437498086418187871599145 7078123564813640903699359)
        ·
          refine ⟨10617185347220461355549039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7078123564813640903699359 10617185347220461355549039)
          ·
            refine ⟨15925778020830692033323559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10617185347220461355549039 15925778020830692033323559)
            ·
              refine ⟨23888667031246038049985339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15925778020830692033323559 23888667031246038049985339)
              ·
                refine ⟨35833000546869057074978009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23888667031246038049985339 35833000546869057074978009)
                ·
                  refine ⟨26874750410151792806233507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35833000546869057074978009 26874750410151792806233507)
                  ·
                    refine ⟨40312125615227689209350261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26874750410151792806233507 40312125615227689209350261)
                    ·
                      refine ⟨3779261776427595863376587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40312125615227689209350261 3779261776427595863376587)
                      ·
                        rfl

theorem cell23_7360086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_7360086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360086 prefixEnd_7360086 := by exact prefixLift 7360086
  have htrace : WordTrace (prefixWord ++ tailWord_7360086) baseStart_7360086 baseEnd_7360086 := by
    simpa [prefixWord, tailWord_7360086, baseEnd_7360086] using wordTrace_append hprefix tailTrace_7360086
  have hstable : (prefixWord ++ tailWord_7360086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360086).length < 2 ^ (prefixWord ++ tailWord_7360086).sum := by decide
  have hdescent : baseEnd_7360086 < baseStart_7360086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360105 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 4, 1, 4]
def baseStart_7360105 : Nat := 118140960795 + 7360105 * 2 ^ 59
def prefixEnd_7360105 : Nat := 4983230072969 + 3 ^ 40 * 7360105 * 2
def baseEnd_7360105 : Nat := 3779271532560031289038999

theorem tailTrace_7360105 : CollatzResearch.WordTrace tailWord_7360105 prefixEnd_7360105 3779271532560031289038999 := by
  unfold tailWord_7360105
  simp only [CollatzResearch.WordTrace]
  refine ⟨268445083000604065703761769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178963388667069377135841179 268445083000604065703761769)
  ·
    refine ⟨201333812250453049277821327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268445083000604065703761769 201333812250453049277821327)
    ·
      refine ⟨302000718375679573916731991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201333812250453049277821327 302000718375679573916731991)
      ·
        refine ⟨453001077563519360875097987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302000718375679573916731991 453001077563519360875097987)
        ·
          refine ⟨679501616345279041312646981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453001077563519360875097987 679501616345279041312646981)
          ·
            refine ⟨127406553064739820246121309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 679501616345279041312646981 127406553064739820246121309)
            ·
              refine ⟨47777457399277432592295491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127406553064739820246121309 47777457399277432592295491)
              ·
                refine ⟨71666186098916148888443237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47777457399277432592295491 71666186098916148888443237)
                ·
                  refine ⟨13437409893546777916583107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71666186098916148888443237 13437409893546777916583107)
                  ·
                    refine ⟨20156114840320166874874661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13437409893546777916583107 20156114840320166874874661)
                    ·
                      refine ⟨3779271532560031289038999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20156114840320166874874661 3779271532560031289038999)
                      ·
                        rfl

theorem cell23_7360105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_7360105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360105 prefixEnd_7360105 := by exact prefixLift 7360105
  have htrace : WordTrace (prefixWord ++ tailWord_7360105) baseStart_7360105 baseEnd_7360105 := by
    simpa [prefixWord, tailWord_7360105, baseEnd_7360105] using wordTrace_append hprefix tailTrace_7360105
  have hstable : (prefixWord ++ tailWord_7360105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360105).length < 2 ^ (prefixWord ++ tailWord_7360105).sum := by decide
  have hdescent : baseEnd_7360105 < baseStart_7360105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360172 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 3]
def baseStart_7360172 : Nat := 118140960795 + 7360172 * 2 ^ 59
def prefixEnd_7360172 : Nat := 4983230072969 + 3 ^ 40 * 7360172 * 2
def baseEnd_7360172 : Nat := 3779305935763882526901191

theorem tailTrace_7360172 : CollatzResearch.WordTrace tailWord_7360172 prefixEnd_7360172 3779305935763882526901191 := by
  unfold tailWord_7360172
  simp only [CollatzResearch.WordTrace]
  refine ⟨134223763345680668073225385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178965017794240890764300513 134223763345680668073225385)
  ·
    refine ⟨100667822509260501054919039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134223763345680668073225385 100667822509260501054919039)
    ·
      refine ⟨151001733763890751582378559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100667822509260501054919039 151001733763890751582378559)
      ·
        refine ⟨226502600645836127373567839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151001733763890751582378559 226502600645836127373567839)
        ·
          refine ⟨339753900968754191060351759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226502600645836127373567839 339753900968754191060351759)
          ·
            refine ⟨509630851453131286590527639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339753900968754191060351759 509630851453131286590527639)
            ·
              refine ⟨764446277179696929885791459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509630851453131286590527639 764446277179696929885791459)
              ·
                refine ⟨1146669415769545394828687189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764446277179696929885791459 1146669415769545394828687189)
                ·
                  refine ⟨6718766108024680047824339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1146669415769545394828687189 6718766108024680047824339)
                  ·
                    refine ⟨10078149162037020071736509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6718766108024680047824339 10078149162037020071736509)
                    ·
                      refine ⟨3779305935763882526901191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10078149162037020071736509 3779305935763882526901191)
                      ·
                        rfl

theorem cell23_7360172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_7360172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360172 prefixEnd_7360172 := by exact prefixLift 7360172
  have htrace : WordTrace (prefixWord ++ tailWord_7360172) baseStart_7360172 baseEnd_7360172 := by
    simpa [prefixWord, tailWord_7360172, baseEnd_7360172] using wordTrace_append hprefix tailTrace_7360172
  have hstable : (prefixWord ++ tailWord_7360172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360172).length < 2 ^ (prefixWord ++ tailWord_7360172).sum := by decide
  have hdescent : baseEnd_7360172 < baseStart_7360172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360175 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 5, 5]
def baseStart_7360175 : Nat := 118140960795 + 7360175 * 2 ^ 59
def prefixEnd_7360175 : Nat := 4983230072969 + 3 ^ 40 * 7360175 * 2
def baseEnd_7360175 : Nat := 1259769158735282005054559

theorem tailTrace_7360175 : CollatzResearch.WordTrace tailWord_7360175 prefixEnd_7360175 1259769158735282005054559 := by
  unfold tailWord_7360175
  simp only [CollatzResearch.WordTrace]
  refine ⟨268447636110350467658809979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178965090740233645105873319 268447636110350467658809979)
  ·
    refine ⟨402671454165525701488214969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268447636110350467658809979 402671454165525701488214969)
    ·
      refine ⟨302003590624144276116161227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402671454165525701488214969 302003590624144276116161227)
      ·
        refine ⟨453005385936216414174241841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302003590624144276116161227 453005385936216414174241841)
        ·
          refine ⟨339754039452162310630681381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453005385936216414174241841 339754039452162310630681381)
          ·
            refine ⟨63703882397280433243252759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339754039452162310630681381 63703882397280433243252759)
            ·
              refine ⟨95555823595920649864879139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63703882397280433243252759 95555823595920649864879139)
              ·
                refine ⟨143333735393880974797318709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95555823595920649864879139 143333735393880974797318709)
                ·
                  refine ⟨13437537693176341387248629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143333735393880974797318709 13437537693176341387248629)
                  ·
                    refine ⟨1259769158735282005054559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13437537693176341387248629 1259769158735282005054559)
                    ·
                      rfl

theorem cell23_7360175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 5].length) (baseStart_7360175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360175 prefixEnd_7360175 := by exact prefixLift 7360175
  have htrace : WordTrace (prefixWord ++ tailWord_7360175) baseStart_7360175 baseEnd_7360175 := by
    simpa [prefixWord, tailWord_7360175, baseEnd_7360175] using wordTrace_append hprefix tailTrace_7360175
  have hstable : (prefixWord ++ tailWord_7360175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360175).length < 2 ^ (prefixWord ++ tailWord_7360175).sum := by decide
  have hdescent : baseEnd_7360175 < baseStart_7360175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360189 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 3, 1, 3]
def baseStart_7360189 : Nat := 118140960795 + 7360189 * 2 ^ 59
def prefixEnd_7360189 : Nat := 4983230072969 + 3 ^ 40 * 7360189 * 2
def baseEnd_7360189 : Nat := 3779314664935008960388613

theorem tailTrace_7360189 : CollatzResearch.WordTrace tailWord_7360189 prefixEnd_7360189 3779314664935008960388613 := by
  unfold tailWord_7360189
  simp only [CollatzResearch.WordTrace]
  refine ⟨268448146732299748049819621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178965431154866498699879747 268448146732299748049819621)
  ·
    refine ⟨50334027512306202759341179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268448146732299748049819621 50334027512306202759341179)
    ·
      refine ⟨75501041268459304139011769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50334027512306202759341179 75501041268459304139011769)
      ·
        refine ⟨56625780951344478104258827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75501041268459304139011769 56625780951344478104258827)
        ·
          refine ⟨84938671427016717156388241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56625780951344478104258827 84938671427016717156388241)
          ·
            refine ⟨63704003570262537867291181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84938671427016717156388241 63704003570262537867291181)
            ·
              refine ⟨23889001338848451700234193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63704003570262537867291181 23889001338848451700234193)
              ·
                refine ⟨17916751004136338775175645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23889001338848451700234193 17916751004136338775175645)
                ·
                  refine ⟨6718781626551127040690867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17916751004136338775175645 6718781626551127040690867)
                  ·
                    refine ⟨10078172439826690561036301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6718781626551127040690867 10078172439826690561036301)
                    ·
                      refine ⟨3779314664935008960388613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10078172439826690561036301 3779314664935008960388613)
                      ·
                        rfl

theorem cell23_7360189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_7360189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360189 prefixEnd_7360189 := by exact prefixLift 7360189
  have htrace : WordTrace (prefixWord ++ tailWord_7360189) baseStart_7360189 baseEnd_7360189 := by
    simpa [prefixWord, tailWord_7360189, baseEnd_7360189] using wordTrace_append hprefix tailTrace_7360189
  have hstable : (prefixWord ++ tailWord_7360189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360189).length < 2 ^ (prefixWord ++ tailWord_7360189).sum := by decide
  have hdescent : baseEnd_7360189 < baseStart_7360189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360192 : List Nat := [2, 1, 1, 2, 4, 1, 2, 4, 1, 5]
def baseStart_7360192 : Nat := 118140960795 + 7360192 * 2 ^ 59
def prefixEnd_7360192 : Nat := 4983230072969 + 3 ^ 40 * 7360192 * 2
def baseEnd_7360192 : Nat := 1259772068458990816217033

theorem tailTrace_7360192 : CollatzResearch.WordTrace tailWord_7360192 prefixEnd_7360192 1259772068458990816217033 := by
  unfold tailWord_7360192
  simp only [CollatzResearch.WordTrace]
  refine ⟨134224128075644439781089415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178965504100859253041452553 134224128075644439781089415)
  ·
    refine ⟨201336192113466659671634123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134224128075644439781089415 201336192113466659671634123)
    ·
      refine ⟨302004288170199989507451185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201336192113466659671634123 302004288170199989507451185)
      ·
        refine ⟨226503216127649992130588389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302004288170199989507451185 226503216127649992130588389)
        ·
          refine ⟨42469353023934373524485323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226503216127649992130588389 42469353023934373524485323)
          ·
            refine ⟨63704029535901560286727985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42469353023934373524485323 63704029535901560286727985)
            ·
              refine ⟨47778022151926170215045989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63704029535901560286727985 47778022151926170215045989)
              ·
                refine ⟨8958379153486156915321123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47778022151926170215045989 8958379153486156915321123)
                ·
                  refine ⟨13437568730229235372981685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8958379153486156915321123 13437568730229235372981685)
                  ·
                    refine ⟨1259772068458990816217033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13437568730229235372981685 1259772068458990816217033)
                    ·
                      rfl

theorem cell23_7360192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 1, 5].length) (baseStart_7360192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360192 prefixEnd_7360192 := by exact prefixLift 7360192
  have htrace : WordTrace (prefixWord ++ tailWord_7360192) baseStart_7360192 baseEnd_7360192 := by
    simpa [prefixWord, tailWord_7360192, baseEnd_7360192] using wordTrace_append hprefix tailTrace_7360192
  have hstable : (prefixWord ++ tailWord_7360192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360192).length < 2 ^ (prefixWord ++ tailWord_7360192).sum := by decide
  have hdescent : baseEnd_7360192 < baseStart_7360192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360209 : List Nat := [1, 2, 2, 1, 2, 4, 4, 1, 1, 5]
def baseStart_7360209 : Nat := 118140960795 + 7360209 * 2 ^ 59
def prefixEnd_7360209 : Nat := 4983230072969 + 3 ^ 40 * 7360209 * 2
def baseEnd_7360209 : Nat := 1259774978182699627379507

theorem tailTrace_7360209 : CollatzResearch.WordTrace tailWord_7360209 prefixEnd_7360209 1259774978182699627379507 := by
  unfold tailWord_7360209
  simp only [CollatzResearch.WordTrace]
  refine ⟨268448876192227291465547681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178965917461484860977031787 268448876192227291465547681)
  ·
    refine ⟨201336657144170468599160761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268448876192227291465547681 201336657144170468599160761)
    ·
      refine ⟨151002492858127851449370571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201336657144170468599160761 151002492858127851449370571)
      ·
        refine ⟨226503739287191777174055857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151002492858127851449370571 226503739287191777174055857)
        ·
          refine ⟨169877804465393832880541893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226503739287191777174055857 169877804465393832880541893)
          ·
            refine ⟨31852088337261343665101605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169877804465393832880541893 31852088337261343665101605)
            ·
              refine ⟨5972266563236501937206551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31852088337261343665101605 5972266563236501937206551)
              ·
                refine ⟨8958399844854752905809827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5972266563236501937206551 8958399844854752905809827)
                ·
                  refine ⟨13437599767282129358714741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8958399844854752905809827 13437599767282129358714741)
                  ·
                    refine ⟨1259774978182699627379507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13437599767282129358714741 1259774978182699627379507)
                    ·
                      rfl

theorem cell23_7360209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_7360209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360209 prefixEnd_7360209 := by exact prefixLift 7360209
  have htrace : WordTrace (prefixWord ++ tailWord_7360209) baseStart_7360209 baseEnd_7360209 := by
    simpa [prefixWord, tailWord_7360209, baseEnd_7360209] using wordTrace_append hprefix tailTrace_7360209
  have hstable : (prefixWord ++ tailWord_7360209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360209).length < 2 ^ (prefixWord ++ tailWord_7360209).sum := by decide
  have hdescent : baseEnd_7360209 < baseStart_7360209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360232 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_7360232 : Nat := 118140960795 + 7360232 * 2 ^ 59
def prefixEnd_7360232 : Nat := 4983230072969 + 3 ^ 40 * 7360232 * 2
def baseEnd_7360232 : Nat := 3779336744603152292150915

theorem tailTrace_7360232 : CollatzResearch.WordTrace tailWord_7360232 prefixEnd_7360232 3779336744603152292150915 := by
  unfold tailWord_7360232
  simp only [CollatzResearch.WordTrace]
  refine ⟨134224857535571983196817475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178966476714095977595756633 134224857535571983196817475)
  ·
    refine ⟨201337286303357974795226213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134224857535571983196817475 201337286303357974795226213)
    ·
      refine ⟨37750741181879620274104915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201337286303357974795226213 37750741181879620274104915)
      ·
        refine ⟨56626111772819430411157373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37750741181879620274104915 56626111772819430411157373)
        ·
          refine ⟨21234791914807286404184015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56626111772819430411157373 21234791914807286404184015)
          ·
            refine ⟨31852187872210929606276023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21234791914807286404184015 31852187872210929606276023)
            ·
              refine ⟨47778281808316394409414035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31852187872210929606276023 47778281808316394409414035)
              ·
                refine ⟨71667422712474591614121053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47778281808316394409414035 71667422712474591614121053)
                ·
                  refine ⟨26875283517177971855295395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71667422712474591614121053 26875283517177971855295395)
                  ·
                    refine ⟨40312925275766957782943093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26875283517177971855295395 40312925275766957782943093)
                    ·
                      refine ⟨3779336744603152292150915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40312925275766957782943093 3779336744603152292150915)
                      ·
                        rfl

theorem cell23_7360232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_7360232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360232 prefixEnd_7360232 := by exact prefixLift 7360232
  have htrace : WordTrace (prefixWord ++ tailWord_7360232) baseStart_7360232 baseEnd_7360232 := by
    simpa [prefixWord, tailWord_7360232, baseEnd_7360232] using wordTrace_append hprefix tailTrace_7360232
  have hstable : (prefixWord ++ tailWord_7360232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360232).length < 2 ^ (prefixWord ++ tailWord_7360232).sum := by decide
  have hdescent : baseEnd_7360232 < baseStart_7360232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360242 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_7360242 : Nat := 118140960795 + 7360242 * 2 ^ 59
def prefixEnd_7360242 : Nat := 4983230072969 + 3 ^ 40 * 7360242 * 2
def baseEnd_7360242 : Nat := 3779341879409697253025869

theorem tailTrace_7360242 : CollatzResearch.WordTrace tailWord_7360242 prefixEnd_7360242 3779341879409697253025869 := by
  unfold tailWord_7360242
  simp only [CollatzResearch.WordTrace]
  refine ⟨67112519950276934525374745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178966719867405158734332653 67112519950276934525374745)
  ·
    refine ⟨50334389962707700894031059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67112519950276934525374745 50334389962707700894031059)
    ·
      refine ⟨75501584944061551341046589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50334389962707700894031059 75501584944061551341046589)
      ·
        refine ⟨28313094354023081752892471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75501584944061551341046589 28313094354023081752892471)
        ·
          refine ⟨42469641531034622629338707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28313094354023081752892471 42469641531034622629338707)
          ·
            refine ⟨63704462296551933944008061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42469641531034622629338707 63704462296551933944008061)
            ·
              refine ⟨23889173361206975229003023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63704462296551933944008061 23889173361206975229003023)
              ·
                refine ⟨35833760041810462843504535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23889173361206975229003023 35833760041810462843504535)
                ·
                  refine ⟨53750640062715694265256803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35833760041810462843504535 53750640062715694265256803)
                  ·
                    refine ⟨80625960094073541397885205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53750640062715694265256803 80625960094073541397885205)
                    ·
                      refine ⟨3779341879409697253025869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80625960094073541397885205 3779341879409697253025869)
                      ·
                        rfl

theorem cell23_7360242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_7360242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360242 prefixEnd_7360242 := by exact prefixLift 7360242
  have htrace : WordTrace (prefixWord ++ tailWord_7360242) baseStart_7360242 baseEnd_7360242 := by
    simpa [prefixWord, tailWord_7360242, baseEnd_7360242] using wordTrace_append hprefix tailTrace_7360242
  have hstable : (prefixWord ++ tailWord_7360242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360242).length < 2 ^ (prefixWord ++ tailWord_7360242).sum := by decide
  have hdescent : baseEnd_7360242 < baseStart_7360242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360246 : List Nat := [5, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_7360246 : Nat := 118140960795 + 7360246 * 2 ^ 59
def prefixEnd_7360246 : Nat := 4983230072969 + 3 ^ 40 * 7360246 * 2
def baseEnd_7360246 : Nat := 3779343933332315237375851

theorem tailTrace_7360246 : CollatzResearch.WordTrace tailWord_7360246 prefixEnd_7360246 3779343933332315237375851 := by
  unfold tailWord_7360246
  simp only [CollatzResearch.WordTrace]
  refine ⟨16778139105818327924040287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178966817128728831189763061 16778139105818327924040287)
  ·
    refine ⟨25167208658727491886060431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16778139105818327924040287 25167208658727491886060431)
    ·
      refine ⟨37750812988091237829090647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25167208658727491886060431 37750812988091237829090647)
      ·
        refine ⟨56626219482136856743635971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37750812988091237829090647 56626219482136856743635971)
        ·
          refine ⟨84939329223205285115453957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56626219482136856743635971 84939329223205285115453957)
          ·
            refine ⟨15926124229350990959147617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84939329223205285115453957 15926124229350990959147617)
            ·
              refine ⟨11944593172013243219360713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15926124229350990959147617 11944593172013243219360713)
              ·
                refine ⟨8958444879009932414520535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11944593172013243219360713 8958444879009932414520535)
                ·
                  refine ⟨13437667318514898621780803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8958444879009932414520535 13437667318514898621780803)
                  ·
                    refine ⟨20156500977772347932671205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13437667318514898621780803 20156500977772347932671205)
                    ·
                      refine ⟨3779343933332315237375851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20156500977772347932671205 3779343933332315237375851)
                      ·
                        rfl

theorem cell23_7360246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_7360246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360246 prefixEnd_7360246 := by exact prefixLift 7360246
  have htrace : WordTrace (prefixWord ++ tailWord_7360246) baseStart_7360246 baseEnd_7360246 := by
    simpa [prefixWord, tailWord_7360246, baseEnd_7360246] using wordTrace_append hprefix tailTrace_7360246
  have hstable : (prefixWord ++ tailWord_7360246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360246).length < 2 ^ (prefixWord ++ tailWord_7360246).sum := by decide
  have hdescent : baseEnd_7360246 < baseStart_7360246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360265 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 1, 9]
def baseStart_7360265 : Nat := 118140960795 + 7360265 * 2 ^ 59
def prefixEnd_7360265 : Nat := 4983230072969 + 3 ^ 40 * 7360265 * 2
def baseEnd_7360265 : Nat := 1259784563154916887679421

theorem tailTrace_7360265 : CollatzResearch.WordTrace tailWord_7360265 prefixEnd_7360265 1259784563154916887679421 := by
  unfold tailWord_7360265
  simp only [CollatzResearch.WordTrace]
  refine ⟨268450918680024413029586249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178967279120016275353057499 268450918680024413029586249)
  ·
    refine ⟨201338189010018309772189687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268450918680024413029586249 201338189010018309772189687)
    ·
      refine ⟨302007283515027464658284531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201338189010018309772189687 302007283515027464658284531)
      ·
        refine ⟨453010925272541196987426797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302007283515027464658284531 453010925272541196987426797)
        ·
          refine ⟨169879096977202948870285049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453010925272541196987426797 169879096977202948870285049)
          ·
            refine ⟨127409322732902211652713787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169879096977202948870285049 127409322732902211652713787)
            ·
              refine ⟨191113984099353317479070681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127409322732902211652713787 191113984099353317479070681)
              ·
                refine ⟨143335488074514988109303011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191113984099353317479070681 143335488074514988109303011)
                ·
                  refine ⟨215003232111772482163954517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143335488074514988109303011 215003232111772482163954517)
                  ·
                    refine ⟨1259784563154916887679421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 215003232111772482163954517 1259784563154916887679421)
                    ·
                      rfl

theorem cell23_7360265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_7360265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360265 prefixEnd_7360265 := by exact prefixLift 7360265
  have htrace : WordTrace (prefixWord ++ tailWord_7360265) baseStart_7360265 baseEnd_7360265 := by
    simpa [prefixWord, tailWord_7360265, baseEnd_7360265] using wordTrace_append hprefix tailTrace_7360265
  have hstable : (prefixWord ++ tailWord_7360265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360265).length < 2 ^ (prefixWord ++ tailWord_7360265).sum := by decide
  have hdescent : baseEnd_7360265 < baseStart_7360265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360306 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2]
def baseStart_7360306 : Nat := 118140960795 + 7360306 * 2 ^ 59
def prefixEnd_7360306 : Nat := 4983230072969 + 3 ^ 40 * 7360306 * 2
def baseEnd_7360306 : Nat := 3779374742171585002625575

theorem tailTrace_7360306 : CollatzResearch.WordTrace tailWord_7360306 prefixEnd_7360306 3779374742171585002625575 := by
  unfold tailWord_7360306
  simp only [CollatzResearch.WordTrace]
  refine ⟨67113103518218969257957193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178968276048583918021219181 67113103518218969257957193)
  ·
    refine ⟨50334827638664226943467895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67113103518218969257957193 50334827638664226943467895)
    ·
      refine ⟨75502241457996340415201843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50334827638664226943467895 75502241457996340415201843)
      ·
        refine ⟨113253362186994510622802765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75502241457996340415201843 113253362186994510622802765)
        ·
          refine ⟨42470010820122941483551037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113253362186994510622802765 42470010820122941483551037)
          ·
            refine ⟨15926254057546103056331639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42470010820122941483551037 15926254057546103056331639)
            ·
              refine ⟨23889381086319154584497459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15926254057546103056331639 23889381086319154584497459)
              ·
                refine ⟨35834071629478731876746189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23889381086319154584497459 35834071629478731876746189)
                ·
                  refine ⟨13437776861054524453779821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35834071629478731876746189 13437776861054524453779821)
                  ·
                    refine ⟨5039166322895446670167433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13437776861054524453779821 5039166322895446670167433)
                    ·
                      refine ⟨3779374742171585002625575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5039166322895446670167433 3779374742171585002625575)
                      ·
                        rfl

theorem cell23_7360306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_7360306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360306 prefixEnd_7360306 := by exact prefixLift 7360306
  have htrace : WordTrace (prefixWord ++ tailWord_7360306) baseStart_7360306 baseEnd_7360306 := by
    simpa [prefixWord, tailWord_7360306, baseEnd_7360306] using wordTrace_append hprefix tailTrace_7360306
  have hstable : (prefixWord ++ tailWord_7360306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360306).length < 2 ^ (prefixWord ++ tailWord_7360306).sum := by decide
  have hdescent : baseEnd_7360306 < baseStart_7360306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360323 : List Nat := [1, 1, 1, 3, 1, 6, 3, 1, 1, 3, 2]
def baseStart_7360323 : Nat := 118140960795 + 7360323 * 2 ^ 59
def prefixEnd_7360323 : Nat := 4983230072969 + 3 ^ 40 * 7360323 * 2
def baseEnd_7360323 : Nat := 3779383471342711436112997

theorem tailTrace_7360323 : CollatzResearch.WordTrace tailWord_7360323 prefixEnd_7360323 3779383471342711436112997 := by
  unfold tailWord_7360323
  simp only [CollatzResearch.WordTrace]
  refine ⟨268453034113814288935197623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178968689409209525956798415 268453034113814288935197623)
  ·
    refine ⟨402679551170721433402796435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268453034113814288935197623 402679551170721433402796435)
    ·
      refine ⟨604019326756082150104194653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402679551170721433402796435 604019326756082150104194653)
      ·
        refine ⟨226507247533530806289072995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 604019326756082150104194653 226507247533530806289072995)
        ·
          refine ⟨339760871300296209433609493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226507247533530806289072995 339760871300296209433609493)
          ·
            refine ⟨15926290842201384817200445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 339760871300296209433609493 15926290842201384817200445)
            ·
              refine ⟨5972359065825519306450167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15926290842201384817200445 5972359065825519306450167)
              ·
                refine ⟨8958538598738278959675251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5972359065825519306450167 8958538598738278959675251)
                ·
                  refine ⟨13437807898107418439512877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8958538598738278959675251 13437807898107418439512877)
                  ·
                    refine ⟨5039177961790281914817329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13437807898107418439512877 5039177961790281914817329)
                    ·
                      refine ⟨3779383471342711436112997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5039177961790281914817329 3779383471342711436112997)
                      ·
                        rfl

theorem cell23_7360323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 1, 3, 2].length) (baseStart_7360323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360323 prefixEnd_7360323 := by exact prefixLift 7360323
  have htrace : WordTrace (prefixWord ++ tailWord_7360323) baseStart_7360323 baseEnd_7360323 := by
    simpa [prefixWord, tailWord_7360323, baseEnd_7360323] using wordTrace_append hprefix tailTrace_7360323
  have hstable : (prefixWord ++ tailWord_7360323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360323).length < 2 ^ (prefixWord ++ tailWord_7360323).sum := by decide
  have hdescent : baseEnd_7360323 < baseStart_7360323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360374 : List Nat := [5, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_7360374 : Nat := 118140960795 + 7360374 * 2 ^ 59
def prefixEnd_7360374 : Nat := 4983230072969 + 3 ^ 40 * 7360374 * 2
def baseEnd_7360374 : Nat := 3779409658856090736575263

theorem tailTrace_7360374 : CollatzResearch.WordTrace tailWord_7360374 prefixEnd_7360374 3779409658856090736575263 := by
  unfold tailWord_7360374
  simp only [CollatzResearch.WordTrace]
  refine ⟨16778430889789345290331511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178969929491086349763536117 16778430889789345290331511)
  ·
    refine ⟨25167646334684017935497267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16778430889789345290331511 25167646334684017935497267)
    ·
      refine ⟨37751469502026026903245901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25167646334684017935497267 37751469502026026903245901)
      ·
        refine ⟨14156801063259760088717213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37751469502026026903245901 14156801063259760088717213)
        ·
          refine ⟨5308800398722410033268955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14156801063259760088717213 5308800398722410033268955)
          ·
            refine ⟨7963200598083615049903433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5308800398722410033268955 7963200598083615049903433)
            ·
              refine ⟨5972400448562711287427575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7963200598083615049903433 5972400448562711287427575)
              ·
                refine ⟨8958600672844066931141363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5972400448562711287427575 8958600672844066931141363)
                ·
                  refine ⟨13437901009266100396712045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8958600672844066931141363 13437901009266100396712045)
                  ·
                    refine ⟨5039212878474787648767017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13437901009266100396712045 5039212878474787648767017)
                    ·
                      refine ⟨3779409658856090736575263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5039212878474787648767017 3779409658856090736575263)
                      ·
                        rfl

theorem cell23_7360374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_7360374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360374 prefixEnd_7360374 := by exact prefixLift 7360374
  have htrace : WordTrace (prefixWord ++ tailWord_7360374) baseStart_7360374 baseEnd_7360374 := by
    simpa [prefixWord, tailWord_7360374, baseEnd_7360374] using wordTrace_append hprefix tailTrace_7360374
  have hstable : (prefixWord ++ tailWord_7360374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360374).length < 2 ^ (prefixWord ++ tailWord_7360374).sum := by decide
  have hdescent : baseEnd_7360374 < baseStart_7360374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360446 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_7360446 : Nat := 118140960795 + 7360446 * 2 ^ 59
def prefixEnd_7360446 : Nat := 4983230072969 + 3 ^ 40 * 7360446 * 2
def baseEnd_7360446 : Nat := 3779446629463214454874931

theorem tailTrace_7360446 : CollatzResearch.WordTrace tailWord_7360446 prefixEnd_7360446 3779446629463214454874931 := by
  unfold tailWord_7360446
  simp only [CollatzResearch.WordTrace]
  refine ⟨33557190036546085117740649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178971680194912453961283461 33557190036546085117740649)
  ·
    refine ⟨25167892527409563838305487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33557190036546085117740649 25167892527409563838305487)
    ·
      refine ⟨37751838791114345757458231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25167892527409563838305487 37751838791114345757458231)
      ·
        refine ⟨56627758186671518636187347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37751838791114345757458231 56627758186671518636187347)
        ·
          refine ⟨84941637280007277954281021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56627758186671518636187347 84941637280007277954281021)
          ·
            refine ⟨31853113980002729232855383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84941637280007277954281021 31853113980002729232855383)
            ·
              refine ⟨47779670970004093849283075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31853113980002729232855383 47779670970004093849283075)
              ·
                refine ⟨71669506455006140773924613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47779670970004093849283075 71669506455006140773924613)
                ·
                  refine ⟨13438032460313651395110865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71669506455006140773924613 13438032460313651395110865)
                  ·
                    refine ⟨10078524345235238546333149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13438032460313651395110865 10078524345235238546333149)
                    ·
                      refine ⟨3779446629463214454874931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10078524345235238546333149 3779446629463214454874931)
                      ·
                        rfl

theorem cell23_7360446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_7360446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360446 prefixEnd_7360446 := by exact prefixLift 7360446
  have htrace : WordTrace (prefixWord ++ tailWord_7360446) baseStart_7360446 baseEnd_7360446 := by
    simpa [prefixWord, tailWord_7360446, baseEnd_7360446] using wordTrace_append hprefix tailTrace_7360446
  have hstable : (prefixWord ++ tailWord_7360446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360446).length < 2 ^ (prefixWord ++ tailWord_7360446).sum := by decide
  have hdescent : baseEnd_7360446 < baseStart_7360446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360526 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_7360526 : Nat := 118140960795 + 7360526 * 2 ^ 59
def prefixEnd_7360526 : Nat := 4983230072969 + 3 ^ 40 * 7360526 * 2
def baseEnd_7360526 : Nat := 1259829235971858047291521

theorem tailTrace_7360526 : CollatzResearch.WordTrace tailWord_7360526 prefixEnd_7360526 1259829235971858047291521 := by
  unfold tailWord_7360526
  simp only [CollatzResearch.WordTrace]
  refine ⟨33557554766509856825604679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178973625421385903069891621 33557554766509856825604679)
  ·
    refine ⟨50336332149764785238407019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33557554766509856825604679 50336332149764785238407019)
    ·
      refine ⟨75504498224647177857610529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50336332149764785238407019 75504498224647177857610529)
      ·
        refine ⟨56628373668485383393207897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75504498224647177857610529 56628373668485383393207897)
        ·
          refine ⟨42471280251364037544905923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56628373668485383393207897 42471280251364037544905923)
          ·
            refine ⟨63706920377046056317358885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42471280251364037544905923 63706920377046056317358885)
            ·
              refine ⟨11945047570696135559504791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63706920377046056317358885 11945047570696135559504791)
              ·
                refine ⟨17917571356044203339257187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11945047570696135559504791 17917571356044203339257187)
                ·
                  refine ⟨26876357034066305008885781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17917571356044203339257187 26876357034066305008885781)
                  ·
                    refine ⟨1259829235971858047291521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26876357034066305008885781 1259829235971858047291521)
                    ·
                      rfl

theorem cell23_7360526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_7360526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360526 prefixEnd_7360526 := by exact prefixLift 7360526
  have htrace : WordTrace (prefixWord ++ tailWord_7360526) baseStart_7360526 baseEnd_7360526 := by
    simpa [prefixWord, tailWord_7360526, baseEnd_7360526] using wordTrace_append hprefix tailTrace_7360526
  have hstable : (prefixWord ++ tailWord_7360526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360526).length < 2 ^ (prefixWord ++ tailWord_7360526).sum := by decide
  have hdescent : baseEnd_7360526 < baseStart_7360526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360536 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 3, 2, 3]
def baseStart_7360536 : Nat := 118140960795 + 7360536 * 2 ^ 59
def prefixEnd_7360536 : Nat := 4983230072969 + 3 ^ 40 * 7360536 * 2
def baseEnd_7360536 : Nat := 3779492842722119102749517

theorem tailTrace_7360536 : CollatzResearch.WordTrace tailWord_7360536 prefixEnd_7360536 3779492842722119102749517 := by
  unfold tailWord_7360536
  simp only [CollatzResearch.WordTrace]
  refine ⟨134230401431021313156350731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178973868574695084208467641 134230401431021313156350731)
  ·
    refine ⟨201345602146531969734526097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134230401431021313156350731 201345602146531969734526097)
    ·
      refine ⟨151009201609898977300894573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201345602146531969734526097 151009201609898977300894573)
      ·
        refine ⟨56628450603712116487835465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151009201609898977300894573 56628450603712116487835465)
        ·
          refine ⟨42471337952784087365876599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56628450603712116487835465 42471337952784087365876599)
          ·
            refine ⟨63707006929176131048814899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42471337952784087365876599 63707006929176131048814899)
            ·
              refine ⟨95560510393764196573222349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63707006929176131048814899 95560510393764196573222349)
              ·
                refine ⟨35835191397661573714958381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95560510393764196573222349 35835191397661573714958381)
                ·
                  refine ⟨13438196774123090143109393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35835191397661573714958381 13438196774123090143109393)
                  ·
                    refine ⟨10078647580592317607332045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13438196774123090143109393 10078647580592317607332045)
                    ·
                      refine ⟨3779492842722119102749517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10078647580592317607332045 3779492842722119102749517)
                      ·
                        rfl

theorem cell23_7360536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_7360536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360536 prefixEnd_7360536 := by exact prefixLift 7360536
  have htrace : WordTrace (prefixWord ++ tailWord_7360536) baseStart_7360536 baseEnd_7360536 := by
    simpa [prefixWord, tailWord_7360536, baseEnd_7360536] using wordTrace_append hprefix tailTrace_7360536
  have hstable : (prefixWord ++ tailWord_7360536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360536).length < 2 ^ (prefixWord ++ tailWord_7360536).sum := by decide
  have hdescent : baseEnd_7360536 < baseStart_7360536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360546 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_7360546 : Nat := 118140960795 + 7360546 * 2 ^ 59
def prefixEnd_7360546 : Nat := 4983230072969 + 3 ^ 40 * 7360546 * 2
def baseEnd_7360546 : Nat := 3779497977528664063624471

theorem tailTrace_7360546 : CollatzResearch.WordTrace tailWord_7360546 prefixEnd_7360546 3779497977528664063624471 := by
  unfold tailWord_7360546
  simp only [CollatzResearch.WordTrace]
  refine ⟨67115291898001599505141373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178974111728004265347043661 67115291898001599505141373)
  ·
    refine ⟨25168234461750599814428015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67115291898001599505141373 25168234461750599814428015)
    ·
      refine ⟨37752351692625899721642023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25168234461750599814428015 37752351692625899721642023)
      ·
        refine ⟨56628527538938849582463035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37752351692625899721642023 56628527538938849582463035)
        ·
          refine ⟨84942791308408274373694553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56628527538938849582463035 84942791308408274373694553)
          ·
            refine ⟨63707093481306205780270915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84942791308408274373694553 63707093481306205780270915)
            ·
              refine ⟨95560640221959308670406373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63707093481306205780270915 95560640221959308670406373)
              ·
                refine ⟨17917620041617370375701195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95560640221959308670406373 17917620041617370375701195)
                ·
                  refine ⟨26876430062426055563551793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17917620041617370375701195 26876430062426055563551793)
                  ·
                    refine ⟨20157322546819541672663845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26876430062426055563551793 20157322546819541672663845)
                    ·
                      refine ⟨3779497977528664063624471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20157322546819541672663845 3779497977528664063624471)
                      ·
                        rfl

theorem cell23_7360546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_7360546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360546 prefixEnd_7360546 := by exact prefixLift 7360546
  have htrace : WordTrace (prefixWord ++ tailWord_7360546) baseStart_7360546 baseEnd_7360546 := by
    simpa [prefixWord, tailWord_7360546, baseEnd_7360546] using wordTrace_append hprefix tailTrace_7360546
  have hstable : (prefixWord ++ tailWord_7360546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360546).length < 2 ^ (prefixWord ++ tailWord_7360546).sum := by decide
  have hdescent : baseEnd_7360546 < baseStart_7360546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360599 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 1, 8]
def baseStart_7360599 : Nat := 118140960795 + 7360599 * 2 ^ 59
def prefixEnd_7360599 : Nat := 4983230072969 + 3 ^ 40 * 7360599 * 2
def baseEnd_7360599 : Nat := 1259841730667784118753909

theorem tailTrace_7360599 : CollatzResearch.WordTrace tailWord_7360599 prefixEnd_7360599 1259841730667784118753909 := by
  unfold tailWord_7360599
  simp only [CollatzResearch.WordTrace]
  refine ⟨268463100660814388072244851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178975400440542925381496567 268463100660814388072244851)
  ·
    refine ⟨402694650991221582108367277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268463100660814388072244851 402694650991221582108367277)
    ·
      refine ⟨151010494121708093290637729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402694650991221582108367277 151010494121708093290637729)
      ·
        refine ⟨113257870591281069967978297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151010494121708093290637729 113257870591281069967978297)
        ·
          refine ⟨84943402943460802475983723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113257870591281069967978297 84943402943460802475983723)
          ·
            refine ⟨127415104415191203713975585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84943402943460802475983723 127415104415191203713975585)
            ·
              refine ⟨95561328311393402785481689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127415104415191203713975585 95561328311393402785481689)
              ·
                refine ⟨71670996233545052089111267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95561328311393402785481689 71670996233545052089111267)
                ·
                  refine ⟨107506494350317578133666901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71670996233545052089111267 107506494350317578133666901)
                  ·
                    refine ⟨1259841730667784118753909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107506494350317578133666901 1259841730667784118753909)
                    ·
                      rfl

theorem cell23_7360599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_7360599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360599 prefixEnd_7360599 := by exact prefixLift 7360599
  have htrace : WordTrace (prefixWord ++ tailWord_7360599) baseStart_7360599 baseEnd_7360599 := by
    simpa [prefixWord, tailWord_7360599, baseEnd_7360599] using wordTrace_append hprefix tailTrace_7360599
  have hstable : (prefixWord ++ tailWord_7360599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360599).length < 2 ^ (prefixWord ++ tailWord_7360599).sum := by decide
  have hdescent : baseEnd_7360599 < baseStart_7360599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360674 : List Nat := [3, 3, 1, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_7360674 : Nat := 118140960795 + 7360674 * 2 ^ 59
def prefixEnd_7360674 : Nat := 4983230072969 + 3 ^ 40 * 7360674 * 2
def baseEnd_7360674 : Nat := 3779563703052439562823883

theorem tailTrace_7360674 : CollatzResearch.WordTrace tailWord_7360674 prefixEnd_7360674 3779563703052439562823883 := by
  unfold tailWord_7360674
  simp only [CollatzResearch.WordTrace]
  refine ⟨67116459033885668970306269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178977224090361783920816717 67116459033885668970306269)
  ·
    refine ⟨25168672137707125863864851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67116459033885668970306269 25168672137707125863864851)
    ·
      refine ⟨37753008206560688795797277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25168672137707125863864851 37753008206560688795797277)
      ·
        refine ⟨14157378077460258298423979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37753008206560688795797277 14157378077460258298423979)
        ·
          refine ⟨21236067116190387447635969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14157378077460258298423979 21236067116190387447635969)
          ·
            refine ⟨15927050337142790585726977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21236067116190387447635969 15927050337142790585726977)
            ·
              refine ⟨11945287752857092939295233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15927050337142790585726977 11945287752857092939295233)
              ·
                refine ⟨8958965814642819704471425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11945287752857092939295233 8958965814642819704471425)
                ·
                  refine ⟨6719224360982114778353569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8958965814642819704471425 6719224360982114778353569)
                  ·
                    refine ⟨5039418270736586083765177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6719224360982114778353569 5039418270736586083765177)
                    ·
                      refine ⟨3779563703052439562823883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5039418270736586083765177 3779563703052439562823883)
                      ·
                        rfl

theorem cell23_7360674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_7360674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360674 prefixEnd_7360674 := by exact prefixLift 7360674
  have htrace : WordTrace (prefixWord ++ tailWord_7360674) baseStart_7360674 baseEnd_7360674 := by
    simpa [prefixWord, tailWord_7360674, baseEnd_7360674] using wordTrace_append hprefix tailTrace_7360674
  have hstable : (prefixWord ++ tailWord_7360674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360674).length < 2 ^ (prefixWord ++ tailWord_7360674).sum := by decide
  have hdescent : baseEnd_7360674 < baseStart_7360674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360696 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_7360696 : Nat := 118140960795 + 7360696 * 2 ^ 59
def prefixEnd_7360696 : Nat := 4983230072969 + 3 ^ 40 * 7360696 * 2
def baseEnd_7360696 : Nat := 3779574999626838476748781

theorem tailTrace_7360696 : CollatzResearch.WordTrace tailWord_7360696 prefixEnd_7360696 3779574999626838476748781 := by
  unfold tailWord_7360696
  simp only [CollatzResearch.WordTrace]
  refine ⟨134233319270731486819262971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178977759027641982425683961 134233319270731486819262971)
  ·
    refine ⟨201349978906097230228894457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134233319270731486819262971 201349978906097230228894457)
    ·
      refine ⟨151012484179572922671670843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201349978906097230228894457 151012484179572922671670843)
      ·
        refine ⟨226518726269359384007506265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151012484179572922671670843 226518726269359384007506265)
        ·
          refine ⟨169889044702019538005629699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226518726269359384007506265 169889044702019538005629699)
          ·
            refine ⟨254833567053029307008444549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169889044702019538005629699 254833567053029307008444549)
            ·
              refine ⟨47781293822442995064083353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254833567053029307008444549 47781293822442995064083353)
              ·
                refine ⟨35835970366832246298062515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47781293822442995064083353 35835970366832246298062515)
                ·
                  refine ⟨53753955550248369447093773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35835970366832246298062515 53753955550248369447093773)
                  ·
                    refine ⟨20157733331343138542660165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53753955550248369447093773 20157733331343138542660165)
                    ·
                      refine ⟨3779574999626838476748781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20157733331343138542660165 3779574999626838476748781)
                      ·
                        rfl

theorem cell23_7360696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_7360696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360696 prefixEnd_7360696 := by exact prefixLift 7360696
  have htrace : WordTrace (prefixWord ++ tailWord_7360696) baseStart_7360696 baseEnd_7360696 := by
    simpa [prefixWord, tailWord_7360696, baseEnd_7360696] using wordTrace_append hprefix tailTrace_7360696
  have hstable : (prefixWord ++ tailWord_7360696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360696).length < 2 ^ (prefixWord ++ tailWord_7360696).sum := by decide
  have hdescent : baseEnd_7360696 < baseStart_7360696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360736 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 8]
def baseStart_7360736 : Nat := 118140960795 + 7360736 * 2 ^ 59
def prefixEnd_7360736 : Nat := 4983230072969 + 3 ^ 40 * 7360736 * 2
def baseEnd_7360736 : Nat := 419955059872557591138733

theorem tailTrace_7360736 : CollatzResearch.WordTrace tailWord_7360736 prefixEnd_7360736 419955059872557591138733 := by
  unfold tailWord_7360736
  simp only [CollatzResearch.WordTrace]
  refine ⟨134234048730659030234991031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178978731640878706979988041 134234048730659030234991031)
  ·
    refine ⟨201351073095988545352486547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134234048730659030234991031 201351073095988545352486547)
    ·
      refine ⟨302026609643982818028729821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201351073095988545352486547 302026609643982818028729821)
      ·
        refine ⟨113259978616493556760773683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302026609643982818028729821 113259978616493556760773683)
        ·
          refine ⟨169889967924740335141160525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113259978616493556760773683 169889967924740335141160525)
          ·
            refine ⟨63708737971777625677935197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169889967924740335141160525 63708737971777625677935197)
            ·
              refine ⟨23890776739416609629225699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63708737971777625677935197 23890776739416609629225699)
              ·
                refine ⟨35836165109124914443838549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23890776739416609629225699 35836165109124914443838549)
                ·
                  refine ⟨419955059872557591138733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35836165109124914443838549 419955059872557591138733)
                  ·
                    rfl

theorem cell23_7360736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 8].length) (baseStart_7360736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360736 prefixEnd_7360736 := by exact prefixLift 7360736
  have htrace : WordTrace (prefixWord ++ tailWord_7360736) baseStart_7360736 baseEnd_7360736 := by
    simpa [prefixWord, tailWord_7360736, baseEnd_7360736] using wordTrace_append hprefix tailTrace_7360736
  have hstable : (prefixWord ++ tailWord_7360736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360736).length < 2 ^ (prefixWord ++ tailWord_7360736).sum := by decide
  have hdescent : baseEnd_7360736 < baseStart_7360736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360803 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 4]
def baseStart_7360803 : Nat := 118140960795 + 7360803 * 2 ^ 59
def prefixEnd_7360803 : Nat := 4983230072969 + 3 ^ 40 * 7360803 * 2
def baseEnd_7360803 : Nat := 3779629942056869558110789

theorem tailTrace_7360803 : CollatzResearch.WordTrace tailWord_7360803 prefixEnd_7360803 3779629942056869558110789 := by
  unfold tailWord_7360803
  simp only [CollatzResearch.WordTrace]
  refine ⟨268470541152075330912671063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178980360768050220608447375 268470541152075330912671063)
  ·
    refine ⟨402705811728112996369006595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268470541152075330912671063 402705811728112996369006595)
    ·
      refine ⟨604058717592169494553509893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402705811728112996369006595 604058717592169494553509893)
      ·
        refine ⟨113261009548531780228783105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 604058717592169494553509893 113261009548531780228783105)
        ·
          refine ⟨84945757161398835171587329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113261009548531780228783105 84945757161398835171587329)
          ·
            refine ⟨63709317871049126378690497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84945757161398835171587329 63709317871049126378690497)
            ·
              refine ⟨47781988403286844784017873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63709317871049126378690497 47781988403286844784017873)
              ·
                refine ⟨35836491302465133588013405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47781988403286844784017873 35836491302465133588013405)
                ·
                  refine ⟨13438684238424425095505027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35836491302465133588013405 13438684238424425095505027)
                  ·
                    refine ⟨20158026357636637643257541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13438684238424425095505027 20158026357636637643257541)
                    ·
                      refine ⟨3779629942056869558110789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20158026357636637643257541 3779629942056869558110789)
                      ·
                        rfl

theorem cell23_7360803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_7360803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360803 prefixEnd_7360803 := by exact prefixLift 7360803
  have htrace : WordTrace (prefixWord ++ tailWord_7360803) baseStart_7360803 baseEnd_7360803 := by
    simpa [prefixWord, tailWord_7360803, baseEnd_7360803] using wordTrace_append hprefix tailTrace_7360803
  have hstable : (prefixWord ++ tailWord_7360803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360803).length < 2 ^ (prefixWord ++ tailWord_7360803).sum := by decide
  have hdescent : baseEnd_7360803 < baseStart_7360803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360817 : List Nat := [1, 2, 2, 3, 4, 2, 1, 2, 1, 5]
def baseStart_7360817 : Nat := 118140960795 + 7360817 * 2 ^ 59
def prefixEnd_7360817 : Nat := 4983230072969 + 3 ^ 40 * 7360817 * 2
def baseEnd_7360817 : Nat := 1259879043595344167778575

theorem tailTrace_7360817 : CollatzResearch.WordTrace tailWord_7360817 prefixEnd_7360817 1259879043595344167778575 := by
  unfold tailWord_7360817
  simp only [CollatzResearch.WordTrace]
  refine ⟨268471051774024611303680705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178980701182683074202453803 268471051774024611303680705)
  ·
    refine ⟨201353288830518458477760529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268471051774024611303680705 201353288830518458477760529)
    ·
      refine ⟨151014966622888843858320397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201353288830518458477760529 151014966622888843858320397)
      ·
        refine ⟨56630612483583316446870149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151014966622888843858320397 56630612483583316446870149)
        ·
          refine ⟨10618239840671871833788153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56630612483583316446870149 10618239840671871833788153)
          ·
            refine ⟨7963679880503903875341115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10618239840671871833788153 7963679880503903875341115)
            ·
              refine ⟨11945519820755855813011673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7963679880503903875341115 11945519820755855813011673)
              ·
                refine ⟨8959139865566891859758755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11945519820755855813011673 8959139865566891859758755)
                ·
                  refine ⟨13438709798350337789638133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8959139865566891859758755 13438709798350337789638133)
                  ·
                    refine ⟨1259879043595344167778575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13438709798350337789638133 1259879043595344167778575)
                    ·
                      rfl

theorem cell23_7360817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_7360817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360817 prefixEnd_7360817 := by exact prefixLift 7360817
  have htrace : WordTrace (prefixWord ++ tailWord_7360817) baseStart_7360817 baseEnd_7360817 := by
    simpa [prefixWord, tailWord_7360817, baseEnd_7360817] using wordTrace_append hprefix tailTrace_7360817
  have hstable : (prefixWord ++ tailWord_7360817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360817).length < 2 ^ (prefixWord ++ tailWord_7360817).sum := by decide
  have hdescent : baseEnd_7360817 < baseStart_7360817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360830 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_7360830 : Nat := 118140960795 + 7360830 * 2 ^ 59
def prefixEnd_7360830 : Nat := 4983230072969 + 3 ^ 40 * 7360830 * 2
def baseEnd_7360830 : Nat := 1259881268678180317491055

theorem tailTrace_7360830 : CollatzResearch.WordTrace tailWord_7360830 prefixEnd_7360830 1259881268678180317491055 := by
  unfold tailWord_7360830
  simp only [CollatzResearch.WordTrace]
  refine ⟨33558940740372189315487993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178981017281985009682602629 33558940740372189315487993)
  ·
    refine ⟨25169205555279141986615995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33558940740372189315487993 25169205555279141986615995)
    ·
      refine ⟨37753808332918712979923993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25169205555279141986615995 37753808332918712979923993)
      ·
        refine ⟨28315356249689034734942995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37753808332918712979923993 28315356249689034734942995)
        ·
          refine ⟨42473034374533552102414493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28315356249689034734942995 42473034374533552102414493)
          ·
            refine ⟨15927387890450082038405435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42473034374533552102414493 15927387890450082038405435)
            ·
              refine ⟨23891081835675123057608153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15927387890450082038405435 23891081835675123057608153)
              ·
                refine ⟨17918311376756342293206115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23891081835675123057608153 17918311376756342293206115)
                ·
                  refine ⟨26877467065134513439809173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17918311376756342293206115 26877467065134513439809173)
                  ·
                    refine ⟨1259881268678180317491055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26877467065134513439809173 1259881268678180317491055)
                    ·
                      rfl

theorem cell23_7360830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_7360830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360830 prefixEnd_7360830 := by exact prefixLift 7360830
  have htrace : WordTrace (prefixWord ++ tailWord_7360830) baseStart_7360830 baseEnd_7360830 := by
    simpa [prefixWord, tailWord_7360830, baseEnd_7360830] using wordTrace_append hprefix tailTrace_7360830
  have hstable : (prefixWord ++ tailWord_7360830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360830).length < 2 ^ (prefixWord ++ tailWord_7360830).sum := by decide
  have hdescent : baseEnd_7360830 < baseStart_7360830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360840 : List Nat := [2, 1, 3, 1, 1, 2, 2, 5, 1, 2, 3]
def baseStart_7360840 : Nat := 118140960795 + 7360840 * 2 ^ 59
def prefixEnd_7360840 : Nat := 4983230072969 + 3 ^ 40 * 7360840 * 2
def baseEnd_7360840 : Nat := 3779648940841085913348119

theorem tailTrace_7360840 : CollatzResearch.WordTrace tailWord_7360840 prefixEnd_7360840 3779648940841085913348119 := by
  unfold tailWord_7360840
  simp only [CollatzResearch.WordTrace]
  refine ⟨134235945326470643115883987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178981260435294190821178649 134235945326470643115883987)
  ·
    refine ⟨201353917989705964673825981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134235945326470643115883987 201353917989705964673825981)
    ·
      refine ⟨75507719246139736752684743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201353917989705964673825981 75507719246139736752684743)
      ·
        refine ⟨113261578869209605129027115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75507719246139736752684743 113261578869209605129027115)
        ·
          refine ⟨169892368303814407693540673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113261578869209605129027115 169892368303814407693540673)
          ·
            refine ⟨127419276227860805770155505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169892368303814407693540673 127419276227860805770155505)
            ·
              refine ⟨95564457170895604327616629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127419276227860805770155505 95564457170895604327616629)
              ·
                refine ⟨8959167859771462905714059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95564457170895604327616629 8959167859771462905714059)
                ·
                  refine ⟨13438751789657194358571089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8959167859771462905714059 13438751789657194358571089)
                  ·
                    refine ⟨10079063842242895768928317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13438751789657194358571089 10079063842242895768928317)
                    ·
                      refine ⟨3779648940841085913348119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10079063842242895768928317 3779648940841085913348119)
                      ·
                        rfl

theorem cell23_7360840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_7360840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360840 prefixEnd_7360840 := by exact prefixLift 7360840
  have htrace : WordTrace (prefixWord ++ tailWord_7360840) baseStart_7360840 baseEnd_7360840 := by
    simpa [prefixWord, tailWord_7360840, baseEnd_7360840] using wordTrace_append hprefix tailTrace_7360840
  have hstable : (prefixWord ++ tailWord_7360840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360840).length < 2 ^ (prefixWord ++ tailWord_7360840).sum := by decide
  have hdescent : baseEnd_7360840 < baseStart_7360840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360898 : List Nat := [3, 4, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_7360898 : Nat := 118140960795 + 7360898 * 2 ^ 59
def prefixEnd_7360898 : Nat := 4983230072969 + 3 ^ 40 * 7360898 * 2
def baseEnd_7360898 : Nat := 1259892907573015562140951

theorem tailTrace_7360898 : CollatzResearch.WordTrace tailWord_7360898 prefixEnd_7360898 1259892907573015562140951 := by
  unfold tailWord_7360898
  simp only [CollatzResearch.WordTrace]
  refine ⟨67118501521682790534344837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178982670724487441424919565 67118501521682790534344837)
  ·
    refine ⟨12584719035315523225189657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67118501521682790534344837 12584719035315523225189657)
    ·
      refine ⟨9438539276486642418892243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12584719035315523225189657 9438539276486642418892243)
      ·
        refine ⟨14157808914729963628338365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9438539276486642418892243 14157808914729963628338365)
        ·
          refine ⟨5309178343023736360626887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14157808914729963628338365 5309178343023736360626887)
          ·
            refine ⟨7963767514535604540940331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5309178343023736360626887 7963767514535604540940331)
            ·
              refine ⟨11945651271803406811410497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7963767514535604540940331 11945651271803406811410497)
              ·
                refine ⟨8959238453852555108557873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11945651271803406811410497 8959238453852555108557873)
                ·
                  refine ⟨6719428840389416331418405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8959238453852555108557873 6719428840389416331418405)
                  ·
                    refine ⟨1259892907573015562140951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6719428840389416331418405 1259892907573015562140951)
                    ·
                      rfl

theorem cell23_7360898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_7360898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360898 prefixEnd_7360898 := by exact prefixLift 7360898
  have htrace : WordTrace (prefixWord ++ tailWord_7360898) baseStart_7360898 baseEnd_7360898 := by
    simpa [prefixWord, tailWord_7360898, baseEnd_7360898] using wordTrace_append hprefix tailTrace_7360898
  have hstable : (prefixWord ++ tailWord_7360898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360898).length < 2 ^ (prefixWord ++ tailWord_7360898).sum := by decide
  have hdescent : baseEnd_7360898 < baseStart_7360898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360903 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 4, 6]
def baseStart_7360903 : Nat := 118140960795 + 7360903 * 2 ^ 59
def prefixEnd_7360903 : Nat := 4983230072969 + 3 ^ 40 * 7360903 * 2
def baseEnd_7360903 : Nat := 1259893763374106388953443

theorem tailTrace_7360903 : CollatzResearch.WordTrace tailWord_7360903 prefixEnd_7360903 1259893763374106388953443 := by
  unfold tailWord_7360903
  simp only [CollatzResearch.WordTrace]
  refine ⟨268474188451713047991311363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178982792301142031994207575 268474188451713047991311363)
  ·
    refine ⟨402711282677569571986967045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268474188451713047991311363 402711282677569571986967045)
    ·
      refine ⟨75508365502044294747556321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 402711282677569571986967045 75508365502044294747556321)
      ·
        refine ⟨56631274126533221060667241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75508365502044294747556321 56631274126533221060667241)
        ·
          refine ⟨42473455594899915795500431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56631274126533221060667241 42473455594899915795500431)
          ·
            refine ⟨63710183392349873693250647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42473455594899915795500431 63710183392349873693250647)
            ·
              refine ⟨95565275088524810539875971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63710183392349873693250647 95565275088524810539875971)
              ·
                refine ⟨143347912632787215809813957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95565275088524810539875971 143347912632787215809813957)
                ·
                  refine ⟨26877733618647602964340117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143347912632787215809813957 26877733618647602964340117)
                  ·
                    refine ⟨1259893763374106388953443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26877733618647602964340117 1259893763374106388953443)
                    ·
                      rfl

theorem cell23_7360903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_7360903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360903 prefixEnd_7360903 := by exact prefixLift 7360903
  have htrace : WordTrace (prefixWord ++ tailWord_7360903) baseStart_7360903 baseEnd_7360903 := by
    simpa [prefixWord, tailWord_7360903, baseEnd_7360903] using wordTrace_append hprefix tailTrace_7360903
  have hstable : (prefixWord ++ tailWord_7360903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360903).length < 2 ^ (prefixWord ++ tailWord_7360903).sum := by decide
  have hdescent : baseEnd_7360903 < baseStart_7360903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360918 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_7360918 : Nat := 118140960795 + 7360918 * 2 ^ 59
def prefixEnd_7360918 : Nat := 4983230072969 + 3 ^ 40 * 7360918 * 2
def baseEnd_7360918 : Nat := 3779688992332136608172761

theorem tailTrace_7360918 : CollatzResearch.WordTrace tailWord_7360918 prefixEnd_7360918 3779688992332136608172761 := by
  unfold tailWord_7360918
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779670971666169097069213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178983157031105803702071605 16779670971666169097069213)
  ·
    refine ⟨6292376614374813411400955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16779670971666169097069213 6292376614374813411400955)
    ·
      refine ⟨9438564921562220117101433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6292376614374813411400955 9438564921562220117101433)
      ·
        refine ⟨7078923691171665087826075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9438564921562220117101433 7078923691171665087826075)
        ·
          refine ⟨10618385536757497631739113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7078923691171665087826075 10618385536757497631739113)
          ·
            refine ⟨7963789152568123223804335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10618385536757497631739113 7963789152568123223804335)
            ·
              refine ⟨11945683728852184835706503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7963789152568123223804335 11945683728852184835706503)
              ·
                refine ⟨17918525593278277253559755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11945683728852184835706503 17918525593278277253559755)
                ·
                  refine ⟨26877788389917415880339633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17918525593278277253559755 26877788389917415880339633)
                  ·
                    refine ⟨20158341292438061910254725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26877788389917415880339633 20158341292438061910254725)
                    ·
                      refine ⟨3779688992332136608172761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20158341292438061910254725 3779688992332136608172761)
                      ·
                        rfl

theorem cell23_7360918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_7360918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360918 prefixEnd_7360918 := by exact prefixLift 7360918
  have htrace : WordTrace (prefixWord ++ tailWord_7360918) baseStart_7360918 baseEnd_7360918 := by
    simpa [prefixWord, tailWord_7360918, baseEnd_7360918] using wordTrace_append hprefix tailTrace_7360918
  have hstable : (prefixWord ++ tailWord_7360918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360918).length < 2 ^ (prefixWord ++ tailWord_7360918).sum := by decide
  have hdescent : baseEnd_7360918 < baseStart_7360918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360920 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 2, 6]
def baseStart_7360920 : Nat := 118140960795 + 7360920 * 2 ^ 59
def prefixEnd_7360920 : Nat := 4983230072969 + 3 ^ 40 * 7360920 * 2
def baseEnd_7360920 : Nat := 1259896673097815200115917

theorem tailTrace_7360920 : CollatzResearch.WordTrace tailWord_7360920 prefixEnd_7360920 1259896673097815200115917 := by
  unfold tailWord_7360920
  simp only [CollatzResearch.WordTrace]
  refine ⟨134237404246325729947340107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178983205661767639929786809 134237404246325729947340107)
  ·
    refine ⟨201356106369488594921010161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134237404246325729947340107 201356106369488594921010161)
    ·
      refine ⟨151017079777116446190757621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201356106369488594921010161 151017079777116446190757621)
      ·
        refine ⟨14157851229104666830383527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151017079777116446190757621 14157851229104666830383527)
        ·
          refine ⟨21236776843657000245575291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14157851229104666830383527 21236776843657000245575291)
          ·
            refine ⟨31855165265485500368362937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21236776843657000245575291 31855165265485500368362937)
            ·
              refine ⟨23891373949114125276272203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31855165265485500368362937 23891373949114125276272203)
              ·
                refine ⟨35837060923671187914408305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23891373949114125276272203 35837060923671187914408305)
                ·
                  refine ⟨26877795692753390935806229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35837060923671187914408305 26877795692753390935806229)
                  ·
                    refine ⟨1259896673097815200115917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26877795692753390935806229 1259896673097815200115917)
                    ·
                      rfl

theorem cell23_7360920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_7360920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360920 prefixEnd_7360920 := by exact prefixLift 7360920
  have htrace : WordTrace (prefixWord ++ tailWord_7360920) baseStart_7360920 baseEnd_7360920 := by
    simpa [prefixWord, tailWord_7360920, baseEnd_7360920] using wordTrace_append hprefix tailTrace_7360920
  have hstable : (prefixWord ++ tailWord_7360920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360920).length < 2 ^ (prefixWord ++ tailWord_7360920).sum := by decide
  have hdescent : baseEnd_7360920 < baseStart_7360920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360930 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_7360930 : Nat := 118140960795 + 7360930 * 2 ^ 59
def prefixEnd_7360930 : Nat := 4983230072969 + 3 ^ 40 * 7360930 * 2
def baseEnd_7360930 : Nat := 3779695154099990561222705

theorem tailTrace_7360930 : CollatzResearch.WordTrace tailWord_7360930 prefixEnd_7360930 3779695154099990561222705 := by
  unfold tailWord_7360930
  simp only [CollatzResearch.WordTrace]
  refine ⟨67118793305653807900636061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178983448815076821068362829 67118793305653807900636061)
  ·
    refine ⟨25169547489620177962738523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67118793305653807900636061 25169547489620177962738523)
    ·
      refine ⟨37754321234430266944107785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25169547489620177962738523 37754321234430266944107785)
      ·
        refine ⟨28315740925822700208080839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37754321234430266944107785 28315740925822700208080839)
        ·
          refine ⟨42473611388734050312121259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28315740925822700208080839 42473611388734050312121259)
          ·
            refine ⟨63710417083101075468181889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42473611388734050312121259 63710417083101075468181889)
            ·
              refine ⟨47782812812325806601136417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63710417083101075468181889 47782812812325806601136417)
              ·
                refine ⟨35837109609244354950852313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47782812812325806601136417 35837109609244354950852313)
                ·
                  refine ⟨26877832206933266213139235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35837109609244354950852313 26877832206933266213139235)
                  ·
                    refine ⟨40316748310399899319708853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26877832206933266213139235 40316748310399899319708853)
                    ·
                      refine ⟨3779695154099990561222705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40316748310399899319708853 3779695154099990561222705)
                      ·
                        rfl

theorem cell23_7360930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_7360930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360930 prefixEnd_7360930 := by exact prefixLift 7360930
  have htrace : WordTrace (prefixWord ++ tailWord_7360930) baseStart_7360930 baseEnd_7360930 := by
    simpa [prefixWord, tailWord_7360930, baseEnd_7360930] using wordTrace_append hprefix tailTrace_7360930
  have hstable : (prefixWord ++ tailWord_7360930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360930).length < 2 ^ (prefixWord ++ tailWord_7360930).sum := by decide
  have hdescent : baseEnd_7360930 < baseStart_7360930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360933 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 7]
def baseStart_7360933 : Nat := 118140960795 + 7360933 * 2 ^ 59
def prefixEnd_7360933 : Nat := 4983230072969 + 3 ^ 40 * 7360933 * 2
def baseEnd_7360933 : Nat := 419966299393550449942799

theorem tailTrace_7360933 : CollatzResearch.WordTrace tailWord_7360933 prefixEnd_7360933 419966299393550449942799 := by
  unfold tailWord_7360933
  simp only [CollatzResearch.WordTrace]
  refine ⟨268475282641604363114903453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178983521761069575409935635 268475282641604363114903453)
  ·
    refine ⟨100678230990601636168088795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268475282641604363114903453 100678230990601636168088795)
    ·
      refine ⟨151017346485902454252133193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100678230990601636168088795 151017346485902454252133193)
      ·
        refine ⟨113263009864426840689099895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151017346485902454252133193 113263009864426840689099895)
        ·
          refine ⟨169894514796640261033649843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113263009864426840689099895 169894514796640261033649843)
          ·
            refine ⟨254841772194960391550474765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169894514796640261033649843 254841772194960391550474765)
            ·
              refine ⟨95565664573110146831428037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254841772194960391550474765 95565664573110146831428037)
              ·
                refine ⟨17918562107458152530892757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95565664573110146831428037 17918562107458152530892757)
                ·
                  refine ⟨419966299393550449942799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17918562107458152530892757 419966299393550449942799)
                  ·
                    rfl

theorem cell23_7360933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_7360933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360933 prefixEnd_7360933 := by exact prefixLift 7360933
  have htrace : WordTrace (prefixWord ++ tailWord_7360933) baseStart_7360933 baseEnd_7360933 := by
    simpa [prefixWord, tailWord_7360933, baseEnd_7360933] using wordTrace_append hprefix tailTrace_7360933
  have hstable : (prefixWord ++ tailWord_7360933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360933).length < 2 ^ (prefixWord ++ tailWord_7360933).sum := by decide
  have hdescent : baseEnd_7360933 < baseStart_7360933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7360978 : List Nat := [3, 2, 2, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_7360978 : Nat := 118140960795 + 7360978 * 2 ^ 59
def prefixEnd_7360978 : Nat := 4983230072969 + 3 ^ 40 * 7360978 * 2
def baseEnd_7360978 : Nat := 3779719801171406373422485

theorem tailTrace_7360978 : CollatzResearch.WordTrace tailWord_7360978 prefixEnd_7360978 3779719801171406373422485 := by
  unfold tailWord_7360978
  simp only [CollatzResearch.WordTrace]
  refine ⟨67119230981610333950072897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178984615950960890533527725 67119230981610333950072897)
  ·
    refine ⟨50339423236207750462554673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67119230981610333950072897 50339423236207750462554673)
    ·
      refine ⟨37754567427155812846916005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50339423236207750462554673 37754567427155812846916005)
      ·
        refine ⟨7078981392591714908796751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37754567427155812846916005 7078981392591714908796751)
        ·
          refine ⟨10618472088887572363195127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7078981392591714908796751 10618472088887572363195127)
          ·
            refine ⟨15927708133331358544792691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10618472088887572363195127 15927708133331358544792691)
            ·
              refine ⟨23891562199997037817189037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15927708133331358544792691 23891562199997037817189037)
              ·
                refine ⟨8959335824998889181445889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23891562199997037817189037 8959335824998889181445889)
                ·
                  refine ⟨6719501868749166886084417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8959335824998889181445889 6719501868749166886084417)
                  ·
                    refine ⟨5039626401561875164563313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6719501868749166886084417 5039626401561875164563313)
                    ·
                      refine ⟨3779719801171406373422485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5039626401561875164563313 3779719801171406373422485)
                      ·
                        rfl

theorem cell23_7360978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_7360978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7360978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7360978 prefixEnd_7360978 := by exact prefixLift 7360978
  have htrace : WordTrace (prefixWord ++ tailWord_7360978) baseStart_7360978 baseEnd_7360978 := by
    simpa [prefixWord, tailWord_7360978, baseEnd_7360978] using wordTrace_append hprefix tailTrace_7360978
  have hstable : (prefixWord ++ tailWord_7360978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7360978).length < 2 ^ (prefixWord ++ tailWord_7360978).sum := by decide
  have hdescent : baseEnd_7360978 < baseStart_7360978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7360978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361020 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_7361020 : Nat := 118140960795 + 7361020 * 2 ^ 59
def prefixEnd_7361020 : Nat := 4983230072969 + 3 ^ 40 * 7361020 * 2
def baseEnd_7361020 : Nat := 3779741367358895209097291

theorem tailTrace_7361020 : CollatzResearch.WordTrace tailWord_7361020 prefixEnd_7361020 3779741367358895209097291 := by
  unfold tailWord_7361020
  simp only [CollatzResearch.WordTrace]
  refine ⟨134239227896144588486660257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178985637194859451315547009 134239227896144588486660257)
  ·
    refine ⟨100679420922108441364995193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134239227896144588486660257 100679420922108441364995193)
    ·
      refine ⟨75509565691581331023746395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100679420922108441364995193 75509565691581331023746395)
      ·
        refine ⟨113264348537371996535619593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75509565691581331023746395 113264348537371996535619593)
        ·
          refine ⟨84948261403028997401714695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113264348537371996535619593 84948261403028997401714695)
          ·
            refine ⟨127422392104543496102572043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84948261403028997401714695 127422392104543496102572043)
            ·
              refine ⟨191133588156815244153858065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127422392104543496102572043 191133588156815244153858065)
              ·
                refine ⟨143350191117611433115393549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191133588156815244153858065 143350191117611433115393549)
                ·
                  refine ⟨53756321669104287418272581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143350191117611433115393549 53756321669104287418272581)
                  ·
                    refine ⟨10079310312957053890926109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53756321669104287418272581 10079310312957053890926109)
                    ·
                      refine ⟨3779741367358895209097291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10079310312957053890926109 3779741367358895209097291)
                      ·
                        rfl

theorem cell23_7361020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_7361020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361020 prefixEnd_7361020 := by exact prefixLift 7361020
  have htrace : WordTrace (prefixWord ++ tailWord_7361020) baseStart_7361020 baseEnd_7361020 := by
    simpa [prefixWord, tailWord_7361020, baseEnd_7361020] using wordTrace_append hprefix tailTrace_7361020
  have hstable : (prefixWord ++ tailWord_7361020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361020).length < 2 ^ (prefixWord ++ tailWord_7361020).sum := by decide
  have hdescent : baseEnd_7361020 < baseStart_7361020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361044 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_7361044 : Nat := 118140960795 + 7361044 * 2 ^ 59
def prefixEnd_7361044 : Nat := 4983230072969 + 3 ^ 40 * 7361044 * 2
def baseEnd_7361044 : Nat := 1259917896964867705065727

theorem tailTrace_7361044 : CollatzResearch.WordTrace tailWord_7361044 prefixEnd_7361044 1259917896964867705065727 := by
  unfold tailWord_7361044
  simp only [CollatzResearch.WordTrace]
  refine ⟨134239665572101114536097093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178986220762801486048129457 134239665572101114536097093)
  ·
    refine ⟨25169937294768958975518205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134239665572101114536097093 25169937294768958975518205)
    ·
      refine ⟨9438726485538359615819327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25169937294768958975518205 9438726485538359615819327)
      ·
        refine ⟨14158089728307539423728991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9438726485538359615819327 14158089728307539423728991)
        ·
          refine ⟨21237134592461309135593487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14158089728307539423728991 21237134592461309135593487)
          ·
            refine ⟨31855701888691963703390231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21237134592461309135593487 31855701888691963703390231)
            ·
              refine ⟨47783552833037945555085347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31855701888691963703390231 47783552833037945555085347)
              ·
                refine ⟨71675329249556918332628021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47783552833037945555085347 71675329249556918332628021)
                ·
                  refine ⟨6719562117145961093683877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71675329249556918332628021 6719562117145961093683877)
                  ·
                    refine ⟨1259917896964867705065727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6719562117145961093683877 1259917896964867705065727)
                    ·
                      rfl

theorem cell23_7361044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_7361044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361044 prefixEnd_7361044 := by exact prefixLift 7361044
  have htrace : WordTrace (prefixWord ++ tailWord_7361044) baseStart_7361044 baseEnd_7361044 := by
    simpa [prefixWord, tailWord_7361044, baseEnd_7361044] using wordTrace_append hprefix tailTrace_7361044
  have hstable : (prefixWord ++ tailWord_7361044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361044).length < 2 ^ (prefixWord ++ tailWord_7361044).sum := by decide
  have hdescent : baseEnd_7361044 < baseStart_7361044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361084 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 3, 1, 3]
def baseStart_7361084 : Nat := 118140960795 + 7361084 * 2 ^ 59
def prefixEnd_7361084 : Nat := 4983230072969 + 3 ^ 40 * 7361084 * 2
def baseEnd_7361084 : Nat := 3779774230120782958696997

theorem tailTrace_7361084 : CollatzResearch.WordTrace tailWord_7361084 prefixEnd_7361084 3779774230120782958696997 := by
  unfold tailWord_7361084
  simp only [CollatzResearch.WordTrace]
  refine ⟨134240395032028657951825153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178987193376038210602433537 134240395032028657951825153)
  ·
    refine ⟨100680296274021493463868865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134240395032028657951825153 100680296274021493463868865)
    ·
      refine ⟨75510222205516120097901649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100680296274021493463868865 75510222205516120097901649)
      ·
        refine ⟨56632666654137090073426237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75510222205516120097901649 56632666654137090073426237)
        ·
          refine ⟨21237249995301408777534839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56632666654137090073426237 21237249995301408777534839)
          ·
            refine ⟨31855874992952113166302259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21237249995301408777534839 31855874992952113166302259)
            ·
              refine ⟨47783812489428169749453389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31855874992952113166302259 47783812489428169749453389)
              ·
                refine ⟨17918929683535563656045021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47783812489428169749453389 17918929683535563656045021)
                ·
                  refine ⟨6719598631325836371016883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17918929683535563656045021 6719598631325836371016883)
                  ·
                    refine ⟨10079397946988754556525325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6719598631325836371016883 10079397946988754556525325)
                    ·
                      refine ⟨3779774230120782958696997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10079397946988754556525325 3779774230120782958696997)
                      ·
                        rfl

theorem cell23_7361084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_7361084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361084 prefixEnd_7361084 := by exact prefixLift 7361084
  have htrace : WordTrace (prefixWord ++ tailWord_7361084) baseStart_7361084 baseEnd_7361084 := by
    simpa [prefixWord, tailWord_7361084, baseEnd_7361084] using wordTrace_append hprefix tailTrace_7361084
  have hstable : (prefixWord ++ tailWord_7361084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361084).length < 2 ^ (prefixWord ++ tailWord_7361084).sum := by decide
  have hdescent : baseEnd_7361084 < baseStart_7361084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361101 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_7361101 : Nat := 118140960795 + 7361101 * 2 ^ 59
def prefixEnd_7361101 : Nat := 4983230072969 + 3 ^ 40 * 7361101 * 2
def baseEnd_7361101 : Nat := 3779782959291909392184419

theorem tailTrace_7361101 : CollatzResearch.WordTrace tailWord_7361101 prefixEnd_7361101 3779782959291909392184419 := by
  unfold tailWord_7361101
  simp only [CollatzResearch.WordTrace]
  refine ⟨268481410104995727807019157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178987606736663818538012771 268481410104995727807019157)
  ·
    refine ⟨12585066098671674740954023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 268481410104995727807019157 12585066098671674740954023)
    ·
      refine ⟨18877599148007512111431035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12585066098671674740954023 18877599148007512111431035)
      ·
        refine ⟨28316398722011268167146553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18877599148007512111431035 28316398722011268167146553)
        ·
          refine ⟨21237299041508451125359915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28316398722011268167146553 21237299041508451125359915)
          ·
            refine ⟨31855948562262676688039873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21237299041508451125359915 31855948562262676688039873)
            ·
              refine ⟨23891961421697007516029905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31855948562262676688039873 23891961421697007516029905)
              ·
                refine ⟨17918971066272755637022429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23891961421697007516029905 17918971066272755637022429)
                ·
                  refine ⟨6719614149852283363883411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17918971066272755637022429 6719614149852283363883411)
                  ·
                    refine ⟨10079421224778425045825117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6719614149852283363883411 10079421224778425045825117)
                    ·
                      refine ⟨3779782959291909392184419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10079421224778425045825117 3779782959291909392184419)
                      ·
                        rfl

theorem cell23_7361101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_7361101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361101 prefixEnd_7361101 := by exact prefixLift 7361101
  have htrace : WordTrace (prefixWord ++ tailWord_7361101) baseStart_7361101 baseEnd_7361101 := by
    simpa [prefixWord, tailWord_7361101, baseEnd_7361101] using wordTrace_append hprefix tailTrace_7361101
  have hstable : (prefixWord ++ tailWord_7361101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361101).length < 2 ^ (prefixWord ++ tailWord_7361101).sum := by decide
  have hdescent : baseEnd_7361101 < baseStart_7361101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361127 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_7361127 : Nat := 118140960795 + 7361127 * 2 ^ 59
def prefixEnd_7361127 : Nat := 4983230072969 + 3 ^ 40 * 7361127 * 2
def baseEnd_7361127 : Nat := 3779796309788926290459299

theorem tailTrace_7361127 : CollatzResearch.WordTrace tailWord_7361127 prefixEnd_7361127 3779796309788926290459299 := by
  unfold tailWord_7361127
  simp only [CollatzResearch.WordTrace]
  refine ⟨268482358402901534247465635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178988238935267689498310423 268482358402901534247465635)
  ·
    refine ⟨402723537604352301371198453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268482358402901534247465635 402723537604352301371198453)
    ·
      refine ⟨37755331650408028253549855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 402723537604352301371198453 37755331650408028253549855)
      ·
        refine ⟨56632997475612042380324783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37755331650408028253549855 56632997475612042380324783)
        ·
          refine ⟨84949496213418063570487175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56632997475612042380324783 84949496213418063570487175)
          ·
            refine ⟨127424244320127095355730763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84949496213418063570487175 127424244320127095355730763)
            ·
              refine ⟨191136366480190643033596145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127424244320127095355730763 191136366480190643033596145)
              ·
                refine ⟨143352274860142982275197109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191136366480190643033596145 143352274860142982275197109)
                ·
                  refine ⟨13439275768138404588299729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143352274860142982275197109 13439275768138404588299729)
                  ·
                    refine ⟨10079456826103803441224797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13439275768138404588299729 10079456826103803441224797)
                    ·
                      refine ⟨3779796309788926290459299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10079456826103803441224797 3779796309788926290459299)
                      ·
                        rfl

theorem cell23_7361127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_7361127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361127 prefixEnd_7361127 := by exact prefixLift 7361127
  have htrace : WordTrace (prefixWord ++ tailWord_7361127) baseStart_7361127 baseEnd_7361127 := by
    simpa [prefixWord, tailWord_7361127, baseEnd_7361127] using wordTrace_append hprefix tailTrace_7361127
  have hstable : (prefixWord ++ tailWord_7361127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361127).length < 2 ^ (prefixWord ++ tailWord_7361127).sum := by decide
  have hdescent : baseEnd_7361127 < baseStart_7361127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361134 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_7361134 : Nat := 118140960795 + 7361134 * 2 ^ 59
def prefixEnd_7361134 : Nat := 4983230072969 + 3 ^ 40 * 7361134 * 2
def baseEnd_7361134 : Nat := 1259933301384502587690589

theorem tailTrace_7361134 : CollatzResearch.WordTrace tailWord_7361134 prefixEnd_7361134 1259933301384502587690589 := by
  unfold tailWord_7361134
  simp only [CollatzResearch.WordTrace]
  refine ⟨33560326714234521805371307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178988409142584116295313637 33560326714234521805371307)
  ·
    refine ⟨50340490071351782708056961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33560326714234521805371307 50340490071351782708056961)
    ·
      refine ⟨37755367553513837031042721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50340490071351782708056961 37755367553513837031042721)
      ·
        refine ⟨28316525665135377773282041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37755367553513837031042721 28316525665135377773282041)
        ·
          refine ⟨21237394248851533329961531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28316525665135377773282041 21237394248851533329961531)
          ·
            refine ⟨31856091373277299994942297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21237394248851533329961531 31856091373277299994942297)
            ·
              refine ⟨23892068529957974996206723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31856091373277299994942297 23892068529957974996206723)
              ·
                refine ⟨35838102794936962494310085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23892068529957974996206723 35838102794936962494310085)
                ·
                  refine ⟨6719644274050680467683141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35838102794936962494310085 6719644274050680467683141)
                  ·
                    refine ⟨1259933301384502587690589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6719644274050680467683141 1259933301384502587690589)
                    ·
                      rfl

theorem cell23_7361134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_7361134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361134 prefixEnd_7361134 := by exact prefixLift 7361134
  have htrace : WordTrace (prefixWord ++ tailWord_7361134) baseStart_7361134 baseEnd_7361134 := by
    simpa [prefixWord, tailWord_7361134, baseEnd_7361134] using wordTrace_append hprefix tailTrace_7361134
  have hstable : (prefixWord ++ tailWord_7361134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361134).length < 2 ^ (prefixWord ++ tailWord_7361134).sum := by decide
  have hdescent : baseEnd_7361134 < baseStart_7361134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361167 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 2, 7, 2]
def baseStart_7361167 : Nat := 118140960795 + 7361167 * 2 ^ 59
def prefixEnd_7361167 : Nat := 4983230072969 + 3 ^ 40 * 7361167 * 2
def baseEnd_7361167 : Nat := 3779816849015106133959115

theorem tailTrace_7361167 : CollatzResearch.WordTrace tailWord_7361167 prefixEnd_7361167 3779816849015106133959115 := by
  unfold tailWord_7361167
  simp only [CollatzResearch.WordTrace]
  refine ⟨268483817322756621078921755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178989211548504414052614503 268483817322756621078921755)
  ·
    refine ⟨402725725984134931618382633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268483817322756621078921755 402725725984134931618382633)
    ·
      refine ⟨302044294488101198713786975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402725725984134931618382633 302044294488101198713786975)
      ·
        refine ⟨453066441732151798070680463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302044294488101198713786975 453066441732151798070680463)
        ·
          refine ⟨679599662598227697106020695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453066441732151798070680463 679599662598227697106020695)
          ·
            refine ⟨1019399493897341545659031043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679599662598227697106020695 1019399493897341545659031043)
            ·
              refine ⟨1529099240846012318488546565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019399493897341545659031043 1529099240846012318488546565)
              ·
                refine ⟨286706107658627309716602481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1529099240846012318488546565 286706107658627309716602481)
                ·
                  refine ⟨215029580743970482287451861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286706107658627309716602481 215029580743970482287451861)
                  ·
                    refine ⟨5039755798686808178612153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 215029580743970482287451861 5039755798686808178612153)
                    ·
                      refine ⟨3779816849015106133959115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5039755798686808178612153 3779816849015106133959115)
                      ·
                        rfl

theorem cell23_7361167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 7, 2].length) (baseStart_7361167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361167 prefixEnd_7361167 := by exact prefixLift 7361167
  have htrace : WordTrace (prefixWord ++ tailWord_7361167) baseStart_7361167 baseEnd_7361167 := by
    simpa [prefixWord, tailWord_7361167, baseEnd_7361167] using wordTrace_append hprefix tailTrace_7361167
  have hstable : (prefixWord ++ tailWord_7361167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361167).length < 2 ^ (prefixWord ++ tailWord_7361167).sum := by decide
  have hdescent : baseEnd_7361167 < baseStart_7361167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361178 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5]
def baseStart_7361178 : Nat := 118140960795 + 7361178 * 2 ^ 59
def prefixEnd_7361178 : Nat := 4983230072969 + 3 ^ 40 * 7361178 * 2
def baseEnd_7361178 : Nat := 3779822497302305590921565

theorem tailTrace_7361178 : CollatzResearch.WordTrace tailWord_7361178 prefixEnd_7361178 3779822497302305590921565 := by
  unfold tailWord_7361178
  simp only [CollatzResearch.WordTrace]
  refine ⟨67121054631429192489393047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178989479017144513305048125 67121054631429192489393047)
  ·
    refine ⟨100681581947143788734089571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67121054631429192489393047 100681581947143788734089571)
    ·
      refine ⟨151022372920715683101134357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100681581947143788734089571 151022372920715683101134357)
      ·
        refine ⟨7079173730658547645365673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151022372920715683101134357 7079173730658547645365673)
        ·
          refine ⟨5309380297993910734024255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7079173730658547645365673 5309380297993910734024255)
          ·
            refine ⟨7964070446990866101036383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5309380297993910734024255 7964070446990866101036383)
            ·
              refine ⟨11946105670486299151554575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7964070446990866101036383 11946105670486299151554575)
              ·
                refine ⟨17919158505729448727331863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11946105670486299151554575 17919158505729448727331863)
                ·
                  refine ⟨26878737758594173090997795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17919158505729448727331863 26878737758594173090997795)
                  ·
                    refine ⟨40318106637891259636496693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26878737758594173090997795 40318106637891259636496693)
                    ·
                      refine ⟨3779822497302305590921565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40318106637891259636496693 3779822497302305590921565)
                      ·
                        rfl

theorem cell23_7361178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_7361178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361178 prefixEnd_7361178 := by exact prefixLift 7361178
  have htrace : WordTrace (prefixWord ++ tailWord_7361178) baseStart_7361178 baseEnd_7361178 := by
    simpa [prefixWord, tailWord_7361178, baseEnd_7361178] using wordTrace_append hprefix tailTrace_7361178
  have hstable : (prefixWord ++ tailWord_7361178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361178).length < 2 ^ (prefixWord ++ tailWord_7361178).sum := by decide
  have hdescent : baseEnd_7361178 < baseStart_7361178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361274 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2]
def baseStart_7361274 : Nat := 118140960795 + 7361274 * 2 ^ 59
def prefixEnd_7361274 : Nat := 4983230072969 + 3 ^ 40 * 7361274 * 2
def baseEnd_7361274 : Nat := 3779871791445137215321123

theorem tailTrace_7361274 : CollatzResearch.WordTrace tailWord_7361274 prefixEnd_7361274 3779871791445137215321123 := by
  unfold tailWord_7361274
  simp only [CollatzResearch.WordTrace]
  refine ⟨67121929983342244588266719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178991813288912652235377917 67121929983342244588266719)
  ·
    refine ⟨100682894975013366882400079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67121929983342244588266719 100682894975013366882400079)
    ·
      refine ⟨151024342462520050323600119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100682894975013366882400079 151024342462520050323600119)
      ·
        refine ⟨226536513693780075485400179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151024342462520050323600119 226536513693780075485400179)
        ·
          refine ⟨339804770540670113228100269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226536513693780075485400179 339804770540670113228100269)
          ·
            refine ⟨127426788952751292460537601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339804770540670113228100269 127426788952751292460537601)
            ·
              refine ⟨95570091714563469345403201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127426788952751292460537601 95570091714563469345403201)
              ·
                refine ⟨71677568785922602009052401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95570091714563469345403201 71677568785922602009052401)
                ·
                  refine ⟨53758176589441951506789301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71677568785922602009052401 53758176589441951506789301)
                  ·
                    refine ⟨5039829055260182953761497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53758176589441951506789301 5039829055260182953761497)
                    ·
                      refine ⟨3779871791445137215321123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5039829055260182953761497 3779871791445137215321123)
                      ·
                        rfl

theorem cell23_7361274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2].length) (baseStart_7361274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361274 prefixEnd_7361274 := by exact prefixLift 7361274
  have htrace : WordTrace (prefixWord ++ tailWord_7361274) baseStart_7361274 baseEnd_7361274 := by
    simpa [prefixWord, tailWord_7361274, baseEnd_7361274] using wordTrace_append hprefix tailTrace_7361274
  have hstable : (prefixWord ++ tailWord_7361274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361274).length < 2 ^ (prefixWord ++ tailWord_7361274).sum := by decide
  have hdescent : baseEnd_7361274 < baseStart_7361274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361284 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_7361284 : Nat := 118140960795 + 7361284 * 2 ^ 59
def prefixEnd_7361284 : Nat := 4983230072969 + 3 ^ 40 * 7361284 * 2
def baseEnd_7361284 : Nat := 1259958975417227392065359

theorem tailTrace_7361284 : CollatzResearch.WordTrace tailWord_7361284 prefixEnd_7361284 1259958975417227392065359 := by
  unfold tailWord_7361284
  simp only [CollatzResearch.WordTrace]
  refine ⟨134244042331666375030465453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178992056442221833373953937 134244042331666375030465453)
  ·
    refine ⟨50341515874374890636424545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134244042331666375030465453 50341515874374890636424545)
    ·
      refine ⟨37756136905781167977318409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50341515874374890636424545 37756136905781167977318409)
      ·
        refine ⟨28317102679335875982988807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37756136905781167977318409 28317102679335875982988807)
        ·
          refine ⟨42475654019003813974483211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28317102679335875982988807 42475654019003813974483211)
          ·
            refine ⟨63713481028505720961724817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42475654019003813974483211 63713481028505720961724817)
            ·
              refine ⟨47785110771379290721293613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63713481028505720961724817 47785110771379290721293613)
              ·
                refine ⟨17919416539267234020485105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47785110771379290721293613 17919416539267234020485105)
                ·
                  refine ⟨13439562404450425515363829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17919416539267234020485105 13439562404450425515363829)
                  ·
                    refine ⟨1259958975417227392065359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13439562404450425515363829 1259958975417227392065359)
                    ·
                      rfl

theorem cell23_7361284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_7361284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361284 prefixEnd_7361284 := by exact prefixLift 7361284
  have htrace : WordTrace (prefixWord ++ tailWord_7361284) baseStart_7361284 baseEnd_7361284 := by
    simpa [prefixWord, tailWord_7361284, baseEnd_7361284] using wordTrace_append hprefix tailTrace_7361284
  have hstable : (prefixWord ++ tailWord_7361284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361284).length < 2 ^ (prefixWord ++ tailWord_7361284).sum := by decide
  have hdescent : baseEnd_7361284 < baseStart_7361284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361324 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 3]
def baseStart_7361324 : Nat := 118140960795 + 7361324 * 2 ^ 59
def prefixEnd_7361324 : Nat := 4983230072969 + 3 ^ 40 * 7361324 * 2
def baseEnd_7361324 : Nat := 3779897465477862019695893

theorem tailTrace_7361324 : CollatzResearch.WordTrace tailWord_7361324 prefixEnd_7361324 3779897465477862019695893 := by
  unfold tailWord_7361324
  simp only [CollatzResearch.WordTrace]
  refine ⟨134244771791593918446193513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178993029055458557928258017 134244771791593918446193513)
  ·
    refine ⟨100683578843695438834645135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134244771791593918446193513 100683578843695438834645135)
    ·
      refine ⟨151025368265543158251967703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100683578843695438834645135 151025368265543158251967703)
      ·
        refine ⟨226538052398314737377951555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151025368265543158251967703 226538052398314737377951555)
        ·
          refine ⟨339807078597472106066927333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226538052398314737377951555 339807078597472106066927333)
          ·
            refine ⟨63713827237026019887548875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339807078597472106066927333 63713827237026019887548875)
            ·
              refine ⟨95570740855539029831323313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63713827237026019887548875 95570740855539029831323313)
              ·
                refine ⟨71678055641654272373492485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95570740855539029831323313 71678055641654272373492485)
                ·
                  refine ⟨13439635432810176070029841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71678055641654272373492485 13439635432810176070029841)
                  ·
                    refine ⟨10079726574607632052522381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13439635432810176070029841 10079726574607632052522381)
                    ·
                      refine ⟨3779897465477862019695893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10079726574607632052522381 3779897465477862019695893)
                      ·
                        rfl

theorem cell23_7361324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_7361324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361324 prefixEnd_7361324 := by exact prefixLift 7361324
  have htrace : WordTrace (prefixWord ++ tailWord_7361324) baseStart_7361324 baseEnd_7361324 := by
    simpa [prefixWord, tailWord_7361324, baseEnd_7361324] using wordTrace_append hprefix tailTrace_7361324
  have hstable : (prefixWord ++ tailWord_7361324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361324).length < 2 ^ (prefixWord ++ tailWord_7361324).sum := by decide
  have hdescent : baseEnd_7361324 < baseStart_7361324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361361 : List Nat := [1, 2, 2, 1, 6, 1, 2, 2, 6]
def baseStart_7361361 : Nat := 118140960795 + 7361361 * 2 ^ 59
def prefixEnd_7361361 : Nat := 4983230072969 + 3 ^ 40 * 7361361 * 2
def baseEnd_7361361 : Nat := 419990718251342041659247

theorem tailTrace_7361361 : CollatzResearch.WordTrace tailWord_7361361 prefixEnd_7361361 419990718251342041659247 := by
  unfold tailWord_7361361
  simp only [CollatzResearch.WordTrace]
  refine ⟨268490893084053792211483937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178993928722702528140989291 268490893084053792211483937)
  ·
    refine ⟨201368169813040344158612953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268490893084053792211483937 201368169813040344158612953)
    ·
      refine ⟨151026127359780258118959715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201368169813040344158612953 151026127359780258118959715)
      ·
        refine ⟨226539191039670387178439573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151026127359780258118959715 226539191039670387178439573)
        ·
          refine ⟨10619024579984549398989355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 226539191039670387178439573 10619024579984549398989355)
          ·
            refine ⟨15928536869976824098484033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10619024579984549398989355 15928536869976824098484033)
            ·
              refine ⟨11946402652482618073863025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15928536869976824098484033 11946402652482618073863025)
              ·
                refine ⟨8959801989361963555397269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11946402652482618073863025 8959801989361963555397269)
                ·
                  refine ⟨419990718251342041659247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8959801989361963555397269 419990718251342041659247)
                  ·
                    rfl

theorem cell23_7361361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 6].length) (baseStart_7361361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361361 prefixEnd_7361361 := by exact prefixLift 7361361
  have htrace : WordTrace (prefixWord ++ tailWord_7361361) baseStart_7361361 baseEnd_7361361 := by
    simpa [prefixWord, tailWord_7361361, baseEnd_7361361] using wordTrace_append hprefix tailTrace_7361361
  have hstable : (prefixWord ++ tailWord_7361361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361361).length < 2 ^ (prefixWord ++ tailWord_7361361).sum := by decide
  have hdescent : baseEnd_7361361 < baseStart_7361361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361381 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 4, 3, 2]
def baseStart_7361381 : Nat := 118140960795 + 7361381 * 2 ^ 59
def prefixEnd_7361381 : Nat := 4983230072969 + 3 ^ 40 * 7361381 * 2
def baseEnd_7361381 : Nat := 3779926733875168296683131

theorem tailTrace_7361381 : CollatzResearch.WordTrace tailWord_7361381 prefixEnd_7361381 3779926733875168296683131 := by
  unfold tailWord_7361381
  simp only [CollatzResearch.WordTrace]
  refine ⟨268491622543981335627211997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178994415029320890418141331 268491622543981335627211997)
  ·
    refine ⟨100684358453993000860204499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268491622543981335627211997 100684358453993000860204499)
    ·
      refine ⟨151026537680989501290306749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100684358453993000860204499 151026537680989501290306749)
      ·
        refine ⟨56634951630371062983865031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151026537680989501290306749 56634951630371062983865031)
        ·
          refine ⟨84952427445556594475797547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56634951630371062983865031 84952427445556594475797547)
          ·
            refine ⟨127428641168334891713696321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84952427445556594475797547 127428641168334891713696321)
            ·
              refine ⟨95571480876251168785272241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127428641168334891713696321 95571480876251168785272241)
              ·
                refine ⟨71678610657188376588954181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95571480876251168785272241 71678610657188376588954181)
                ·
                  refine ⟨13439739498222820610428909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71678610657188376588954181 13439739498222820610428909)
                  ·
                    refine ⟨5039902311833557728910841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13439739498222820610428909 5039902311833557728910841)
                    ·
                      refine ⟨3779926733875168296683131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5039902311833557728910841 3779926733875168296683131)
                      ·
                        rfl

theorem cell23_7361381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_7361381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361381 prefixEnd_7361381 := by exact prefixLift 7361381
  have htrace : WordTrace (prefixWord ++ tailWord_7361381) baseStart_7361381 baseEnd_7361381 := by
    simpa [prefixWord, tailWord_7361381, baseEnd_7361381] using wordTrace_append hprefix tailTrace_7361381
  have hstable : (prefixWord ++ tailWord_7361381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361381).length < 2 ^ (prefixWord ++ tailWord_7361381).sum := by decide
  have hdescent : baseEnd_7361381 < baseStart_7361381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361411 : List Nat := [1, 1, 1, 3, 4, 1, 3, 3, 1, 1, 4]
def baseStart_7361411 : Nat := 118140960795 + 7361411 * 2 ^ 59
def prefixEnd_7361411 : Nat := 4983230072969 + 3 ^ 40 * 7361411 * 2
def baseEnd_7361411 : Nat := 3779942138294803179307993

theorem tailTrace_7361411 : CollatzResearch.WordTrace tailWord_7361411 prefixEnd_7361411 3779942138294803179307993 := by
  unfold tailWord_7361411
  simp only [CollatzResearch.WordTrace]
  refine ⟨268492716733872650750804087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178995144489248433833869391 268492716733872650750804087)
  ·
    refine ⟨402739075100808976126206131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268492716733872650750804087 402739075100808976126206131)
    ·
      refine ⟨604108612651213464189309197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402739075100808976126206131 604108612651213464189309197)
      ·
        refine ⟨226540729744205049070990949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 604108612651213464189309197 226540729744205049070990949)
        ·
          refine ⟨42476386827038446700810803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226540729744205049070990949 42476386827038446700810803)
          ·
            refine ⟨63714580240557670051216205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42476386827038446700810803 63714580240557670051216205)
            ·
              refine ⟨23892967590209126269206077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63714580240557670051216205 23892967590209126269206077)
              ·
                refine ⟨8959862846328422350952279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23892967590209126269206077 8959862846328422350952279)
                ·
                  refine ⟨13439794269492633526428419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8959862846328422350952279 13439794269492633526428419)
                  ·
                    refine ⟨20159691404238950289642629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13439794269492633526428419 20159691404238950289642629)
                    ·
                      refine ⟨3779942138294803179307993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20159691404238950289642629 3779942138294803179307993)
                      ·
                        rfl

theorem cell23_7361411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_7361411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361411 prefixEnd_7361411 := by exact prefixLift 7361411
  have htrace : WordTrace (prefixWord ++ tailWord_7361411) baseStart_7361411 baseEnd_7361411 := by
    simpa [prefixWord, tailWord_7361411, baseEnd_7361411] using wordTrace_append hprefix tailTrace_7361411
  have hstable : (prefixWord ++ tailWord_7361411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361411).length < 2 ^ (prefixWord ++ tailWord_7361411).sum := by decide
  have hdescent : baseEnd_7361411 < baseStart_7361411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361441 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_7361441 : Nat := 118140960795 + 7361441 * 2 ^ 59
def prefixEnd_7361441 : Nat := 4983230072969 + 3 ^ 40 * 7361441 * 2
def baseEnd_7361441 : Nat := 3779957542714438061932855

theorem tailTrace_7361441 : CollatzResearch.WordTrace tailWord_7361441 prefixEnd_7361441 3779957542714438061932855 := by
  unfold tailWord_7361441
  simp only [CollatzResearch.WordTrace]
  refine ⟨268493810923763965874396177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178995873949175977249597451 268493810923763965874396177)
  ·
    refine ⟨201370358192822974405797133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268493810923763965874396177 201370358192822974405797133)
    ·
      refine ⟨75513884322308615402173925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201370358192822974405797133 75513884322308615402173925)
      ·
        refine ⟨14158853310432865387907611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75513884322308615402173925 14158853310432865387907611)
        ·
          refine ⟨21238279965649298081861417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14158853310432865387907611 21238279965649298081861417)
          ·
            refine ⟨15928709974236973561396063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21238279965649298081861417 15928709974236973561396063)
            ·
              refine ⟨23893064961355460342094095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15928709974236973561396063 23893064961355460342094095)
              ·
                refine ⟨35839597442033190513141143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23893064961355460342094095 35839597442033190513141143)
                ·
                  refine ⟨53759396163049785769711715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35839597442033190513141143 53759396163049785769711715)
                  ·
                    refine ⟨80639094244574678654567573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53759396163049785769711715 80639094244574678654567573)
                    ·
                      refine ⟨3779957542714438061932855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80639094244574678654567573 3779957542714438061932855)
                      ·
                        rfl

theorem cell23_7361441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_7361441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361441 prefixEnd_7361441 := by exact prefixLift 7361441
  have htrace : WordTrace (prefixWord ++ tailWord_7361441) baseStart_7361441 baseEnd_7361441 := by
    simpa [prefixWord, tailWord_7361441, baseEnd_7361441] using wordTrace_append hprefix tailTrace_7361441
  have hstable : (prefixWord ++ tailWord_7361441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361441).length < 2 ^ (prefixWord ++ tailWord_7361441).sum := by decide
  have hdescent : baseEnd_7361441 < baseStart_7361441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361461 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_7361461 : Nat := 118140960795 + 7361461 * 2 ^ 59
def prefixEnd_7361461 : Nat := 4983230072969 + 3 ^ 40 * 7361461 * 2
def baseEnd_7361461 : Nat := 3779967812327527983682763

theorem tailTrace_7361461 : CollatzResearch.WordTrace tailWord_7361461 prefixEnd_7361461 3779967812327527983682763 := by
  unfold tailWord_7361461
  simp only [CollatzResearch.WordTrace]
  refine ⟨268494540383691509290124237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178996360255794339526749491 268494540383691509290124237)
  ·
    refine ⟨100685452643884315983796589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268494540383691509290124237 100685452643884315983796589)
    ·
      refine ⟨37757044741456618493923721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100685452643884315983796589 37757044741456618493923721)
      ·
        refine ⟨28317783556092463870442791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37757044741456618493923721 28317783556092463870442791)
        ·
          refine ⟨42476675334138695805664187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28317783556092463870442791 42476675334138695805664187)
          ·
            refine ⟨63715013001208043708496281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42476675334138695805664187 63715013001208043708496281)
            ·
              refine ⟨47786259750906032781372211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63715013001208043708496281 47786259750906032781372211)
              ·
                refine ⟨71679389626359049172058317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47786259750906032781372211 71679389626359049172058317)
                ·
                  refine ⟨26879771109884643439521869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71679389626359049172058317 26879771109884643439521869)
                  ·
                    refine ⟨10079914166206741289820701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26879771109884643439521869 10079914166206741289820701)
                    ·
                      refine ⟨3779967812327527983682763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10079914166206741289820701 3779967812327527983682763)
                      ·
                        rfl

theorem cell23_7361461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_7361461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361461 prefixEnd_7361461 := by exact prefixLift 7361461
  have htrace : WordTrace (prefixWord ++ tailWord_7361461) baseStart_7361461 baseEnd_7361461 := by
    simpa [prefixWord, tailWord_7361461, baseEnd_7361461] using wordTrace_append hprefix tailTrace_7361461
  have hstable : (prefixWord ++ tailWord_7361461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361461).length < 2 ^ (prefixWord ++ tailWord_7361461).sum := by decide
  have hdescent : baseEnd_7361461 < baseStart_7361461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361521 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_7361521 : Nat := 118140960795 + 7361521 * 2 ^ 59
def prefixEnd_7361521 : Nat := 4983230072969 + 3 ^ 40 * 7361521 * 2
def baseEnd_7361521 : Nat := 3779998621166797748932487

theorem tailTrace_7361521 : CollatzResearch.WordTrace tailWord_7361521 prefixEnd_7361521 3779998621166797748932487 := by
  unfold tailWord_7361521
  simp only [CollatzResearch.WordTrace]
  refine ⟨268496728763474139537308417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178997819175649426358205611 268496728763474139537308417)
  ·
    refine ⟨201372546572605604652981313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268496728763474139537308417 201372546572605604652981313)
    ·
      refine ⟨151029409929454203489735985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201372546572605604652981313 151029409929454203489735985)
      ·
        refine ⟨113272057447090652617301989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151029409929454203489735985 113272057447090652617301989)
        ·
          refine ⟨21238510771329497365744123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113272057447090652617301989 21238510771329497365744123)
          ·
            refine ⟨31857766156994246048616185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21238510771329497365744123 31857766156994246048616185)
            ·
              refine ⟨23893324617745684536462139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31857766156994246048616185 23893324617745684536462139)
              ·
                refine ⟨35839986926618526804693209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23893324617745684536462139 35839986926618526804693209)
                ·
                  refine ⟨26879990194963895103519907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35839986926618526804693209 26879990194963895103519907)
                  ·
                    refine ⟨40319985292445842655279861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26879990194963895103519907 40319985292445842655279861)
                    ·
                      refine ⟨3779998621166797748932487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40319985292445842655279861 3779998621166797748932487)
                      ·
                        rfl

theorem cell23_7361521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_7361521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361521 prefixEnd_7361521 := by exact prefixLift 7361521
  have htrace : WordTrace (prefixWord ++ tailWord_7361521) baseStart_7361521 baseEnd_7361521 := by
    simpa [prefixWord, tailWord_7361521, baseEnd_7361521] using wordTrace_append hprefix tailTrace_7361521
  have hstable : (prefixWord ++ tailWord_7361521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361521).length < 2 ^ (prefixWord ++ tailWord_7361521).sum := by decide
  have hdescent : baseEnd_7361521 < baseStart_7361521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361571 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 1, 7]
def baseStart_7361571 : Nat := 118140960795 + 7361571 * 2 ^ 59
def prefixEnd_7361571 : Nat := 4983230072969 + 3 ^ 40 * 7361571 * 2
def baseEnd_7361571 : Nat := 1260008098399840851102419

theorem tailTrace_7361571 : CollatzResearch.WordTrace tailWord_7361571 prefixEnd_7361571 1260008098399840851102419 := by
  unfold tailWord_7361571
  simp only [CollatzResearch.WordTrace]
  refine ⟨268498552413292998076628567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178999034942195332051085711 268498552413292998076628567)
  ·
    refine ⟨402747828619939497114942851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268498552413292998076628567 402747828619939497114942851)
    ·
      refine ⟨604121742929909245672414277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402747828619939497114942851 604121742929909245672414277)
      ·
        refine ⟨113272826799357983563577677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 604121742929909245672414277 113272826799357983563577677)
        ·
          refine ⟨42477310049759243836341629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113272826799357983563577677 42477310049759243836341629)
          ·
            refine ⟨15928991268659716438628111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42477310049759243836341629 15928991268659716438628111)
            ·
              refine ⟨23893486902989574657942167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15928991268659716438628111 23893486902989574657942167)
              ·
                refine ⟨35840230354484361986913251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23893486902989574657942167 35840230354484361986913251)
                ·
                  refine ⟨53760345531726542980369877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35840230354484361986913251 53760345531726542980369877)
                  ·
                    refine ⟨1260008098399840851102419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53760345531726542980369877 1260008098399840851102419)
                    ·
                      rfl

theorem cell23_7361571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 7].length) (baseStart_7361571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361571 prefixEnd_7361571 := by exact prefixLift 7361571
  have htrace : WordTrace (prefixWord ++ tailWord_7361571) baseStart_7361571 baseEnd_7361571 := by
    simpa [prefixWord, tailWord_7361571, baseEnd_7361571] using wordTrace_append hprefix tailTrace_7361571
  have hstable : (prefixWord ++ tailWord_7361571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361571).length < 2 ^ (prefixWord ++ tailWord_7361571).sum := by decide
  have hdescent : baseEnd_7361571 < baseStart_7361571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361575 : List Nat := [1, 1, 7, 1, 1, 1, 1, 5, 5]
def baseStart_7361575 : Nat := 118140960795 + 7361575 * 2 ^ 59
def prefixEnd_7361575 : Nat := 4983230072969 + 3 ^ 40 * 7361575 * 2
def baseEnd_7361575 : Nat := 420002927680237837517471

theorem tailTrace_7361575 : CollatzResearch.WordTrace tailWord_7361575 prefixEnd_7361575 420002927680237837517471 := by
  unfold tailWord_7361575
  simp only [CollatzResearch.WordTrace]
  refine ⟨268498698305278506759774179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178999132203519004506516119 268498698305278506759774179)
  ·
    refine ⟨402748047457917760139661269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268498698305278506759774179 402748047457917760139661269)
    ·
      refine ⟨9439407362294947503273311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 402748047457917760139661269 9439407362294947503273311)
      ·
        refine ⟨14159111043442421254909967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9439407362294947503273311 14159111043442421254909967)
        ·
          refine ⟨21238666565163631882364951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14159111043442421254909967 21238666565163631882364951)
          ·
            refine ⟨31857999847745447823547427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21238666565163631882364951 31857999847745447823547427)
            ·
              refine ⟨47786999771618171735321141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31857999847745447823547427 47786999771618171735321141)
              ·
                refine ⟨4480031228589203600186357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47786999771618171735321141 4480031228589203600186357)
                ·
                  refine ⟨420002927680237837517471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4480031228589203600186357 420002927680237837517471)
                  ·
                    rfl

theorem cell23_7361575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 5].length) (baseStart_7361575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361575 prefixEnd_7361575 := by exact prefixLift 7361575
  have htrace : WordTrace (prefixWord ++ tailWord_7361575) baseStart_7361575 baseEnd_7361575 := by
    simpa [prefixWord, tailWord_7361575, baseEnd_7361575] using wordTrace_append hprefix tailTrace_7361575
  have hstable : (prefixWord ++ tailWord_7361575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361575).length < 2 ^ (prefixWord ++ tailWord_7361575).sum := by decide
  have hdescent : baseEnd_7361575 < baseStart_7361575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361591 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 4]
def baseStart_7361591 : Nat := 118140960795 + 7361591 * 2 ^ 59
def prefixEnd_7361591 : Nat := 4983230072969 + 3 ^ 40 * 7361591 * 2
def baseEnd_7361591 : Nat := 3780034564812612475057165

theorem tailTrace_7361591 : CollatzResearch.WordTrace tailWord_7361591 prefixEnd_7361591 3780034564812612475057165 := by
  unfold tailWord_7361591
  simp only [CollatzResearch.WordTrace]
  refine ⟨268499281873220541492356627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178999521248813694328237751 268499281873220541492356627)
  ·
    refine ⟨402748922809830812238534941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268499281873220541492356627 402748922809830812238534941)
    ·
      refine ⟨151030846053686554589450603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402748922809830812238534941 151030846053686554589450603)
      ·
        refine ⟨226546269080529831884175905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151030846053686554589450603 226546269080529831884175905)
        ·
          refine ⟨169909701810397373913131929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226546269080529831884175905 169909701810397373913131929)
          ·
            refine ⟨127432276357798030434848947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169909701810397373913131929 127432276357798030434848947)
            ·
              refine ⟨191148414536697045652273421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127432276357798030434848947 191148414536697045652273421)
              ·
                refine ⟨71680655451261392119602533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191148414536697045652273421 71680655451261392119602533)
                ·
                  refine ⟨13440122897111511022425475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71680655451261392119602533 13440122897111511022425475)
                  ·
                    refine ⟨20160184345667266533638213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13440122897111511022425475 20160184345667266533638213)
                    ·
                      refine ⟨3780034564812612475057165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20160184345667266533638213 3780034564812612475057165)
                      ·
                        rfl

theorem cell23_7361591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_7361591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361591 prefixEnd_7361591 := by exact prefixLift 7361591
  have htrace : WordTrace (prefixWord ++ tailWord_7361591) baseStart_7361591 baseEnd_7361591 := by
    simpa [prefixWord, tailWord_7361591, baseEnd_7361591] using wordTrace_append hprefix tailTrace_7361591
  have hstable : (prefixWord ++ tailWord_7361591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361591).length < 2 ^ (prefixWord ++ tailWord_7361591).sum := by decide
  have hdescent : baseEnd_7361591 < baseStart_7361591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361608 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 2, 4, 2]
def baseStart_7361608 : Nat := 118140960795 + 7361608 * 2 ^ 59
def prefixEnd_7361608 : Nat := 4983230072969 + 3 ^ 40 * 7361608 * 2
def baseEnd_7361608 : Nat := 3780043293983738908544587

theorem tailTrace_7361608 : CollatzResearch.WordTrace tailWord_7361608 prefixEnd_7361608 3780043293983738908544587 := by
  unfold tailWord_7361608
  simp only [CollatzResearch.WordTrace]
  refine ⟨134249950957079476697862739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178999934609439302263816985 134249950957079476697862739)
  ·
    refine ⟨201374926435619215046794109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134249950957079476697862739 201374926435619215046794109)
    ·
      refine ⟨75515597413357205642547791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201374926435619215046794109 75515597413357205642547791)
      ·
        refine ⟨113273396120035808463821687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75515597413357205642547791 113273396120035808463821687)
        ·
          refine ⟨169910094180053712695732531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113273396120035808463821687 169910094180053712695732531)
          ·
            refine ⟨254865141270080569043598797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169910094180053712695732531 254865141270080569043598797)
            ·
              refine ⟨95574427976280213391349549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254865141270080569043598797 95574427976280213391349549)
              ·
                refine ⟨35840410491105080021756081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95574427976280213391349549 35840410491105080021756081)
                ·
                  refine ⟨26880307868328810016317061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35840410491105080021756081 26880307868328810016317061)
                  ·
                    refine ⟨5040057725311651878059449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26880307868328810016317061 5040057725311651878059449)
                    ·
                      refine ⟨3780043293983738908544587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5040057725311651878059449 3780043293983738908544587)
                      ·
                        rfl

theorem cell23_7361608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_7361608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361608 prefixEnd_7361608 := by exact prefixLift 7361608
  have htrace : WordTrace (prefixWord ++ tailWord_7361608) baseStart_7361608 baseEnd_7361608 := by
    simpa [prefixWord, tailWord_7361608, baseEnd_7361608] using wordTrace_append hprefix tailTrace_7361608
  have hstable : (prefixWord ++ tailWord_7361608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361608).length < 2 ^ (prefixWord ++ tailWord_7361608).sum := by decide
  have hdescent : baseEnd_7361608 < baseStart_7361608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361621 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_7361621 : Nat := 118140960795 + 7361621 * 2 ^ 59
def prefixEnd_7361621 : Nat := 4983230072969 + 3 ^ 40 * 7361621 * 2
def baseEnd_7361621 : Nat := 3780049969232247357682027

theorem tailTrace_7361621 : CollatzResearch.WordTrace tailWord_7361621 prefixEnd_7361621 3780049969232247357682027 := by
  unfold tailWord_7361621
  simp only [CollatzResearch.WordTrace]
  refine ⟨268500376063111856615948717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179000250708741237743965811 268500376063111856615948717)
  ·
    refine ⟨100687641023666946230980769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268500376063111856615948717 100687641023666946230980769)
    ·
      refine ⟨75515730767750209673235577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100687641023666946230980769 75515730767750209673235577)
      ·
        refine ⟨56636798075812657254926683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75515730767750209673235577 56636798075812657254926683)
        ·
          refine ⟨84955197113718985882390025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56636798075812657254926683 84955197113718985882390025)
          ·
            refine ⟨63716397835289239411792519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84955197113718985882390025 63716397835289239411792519)
            ·
              refine ⟨95574596752933859117688779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63716397835289239411792519 95574596752933859117688779)
              ·
                refine ⟨143361895129400788676533169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95574596752933859117688779 143361895129400788676533169)
                ·
                  refine ⟨107521421347050591507399877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143361895129400788676533169 107521421347050591507399877)
                  ·
                    refine ⟨20160266502571985907637477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107521421347050591507399877 20160266502571985907637477)
                    ·
                      refine ⟨3780049969232247357682027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20160266502571985907637477 3780049969232247357682027)
                      ·
                        rfl

theorem cell23_7361621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_7361621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361621 prefixEnd_7361621 := by exact prefixLift 7361621
  have htrace : WordTrace (prefixWord ++ tailWord_7361621) baseStart_7361621 baseEnd_7361621 := by
    simpa [prefixWord, tailWord_7361621, baseEnd_7361621] using wordTrace_append hprefix tailTrace_7361621
  have hstable : (prefixWord ++ tailWord_7361621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361621).length < 2 ^ (prefixWord ++ tailWord_7361621).sum := by decide
  have hdescent : baseEnd_7361621 < baseStart_7361621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361628 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_7361628 : Nat := 118140960795 + 7361628 * 2 ^ 59
def prefixEnd_7361628 : Nat := 4983230072969 + 3 ^ 40 * 7361628 * 2
def baseEnd_7361628 : Nat := 3780053563596828830294495

theorem tailTrace_7361628 : CollatzResearch.WordTrace tailWord_7361628 prefixEnd_7361628 3780053563596828830294495 := by
  unfold tailWord_7361628
  simp only [CollatzResearch.WordTrace]
  refine ⟨134250315687043248405726769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179000420916057664540969025 134250315687043248405726769)
  ·
    refine ⟨100687736765282436304295077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134250315687043248405726769 100687736765282436304295077)
    ·
      refine ⟨18878950643490456807055327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100687736765282436304295077 18878950643490456807055327)
      ·
        refine ⟨28318425965235685210582991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18878950643490456807055327 28318425965235685210582991)
        ·
          refine ⟨42477638947853527815874487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28318425965235685210582991 42477638947853527815874487)
          ·
            refine ⟨63716458421780291723811731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42477638947853527815874487 63716458421780291723811731)
            ·
              refine ⟨95574687632670437585717597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63716458421780291723811731 95574687632670437585717597)
              ·
                refine ⟨35840507862251414094644099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95574687632670437585717597 35840507862251414094644099)
                ·
                  refine ⟨53760761793377121141966149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35840507862251414094644099 53760761793377121141966149)
                  ·
                    refine ⟨10080142836258210214118653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53760761793377121141966149 10080142836258210214118653)
                    ·
                      refine ⟨3780053563596828830294495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10080142836258210214118653 3780053563596828830294495)
                      ·
                        rfl

theorem cell23_7361628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_7361628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361628 prefixEnd_7361628 := by exact prefixLift 7361628
  have htrace : WordTrace (prefixWord ++ tailWord_7361628) baseStart_7361628 baseEnd_7361628 := by
    simpa [prefixWord, tailWord_7361628, baseEnd_7361628] using wordTrace_append hprefix tailTrace_7361628
  have hstable : (prefixWord ++ tailWord_7361628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361628).length < 2 ^ (prefixWord ++ tailWord_7361628).sum := by decide
  have hdescent : baseEnd_7361628 < baseStart_7361628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361645 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_7361645 : Nat := 118140960795 + 7361645 * 2 ^ 59
def prefixEnd_7361645 : Nat := 4983230072969 + 3 ^ 40 * 7361645 * 2
def baseEnd_7361645 : Nat := 3780062292767955263781917

theorem tailTrace_7361645 : CollatzResearch.WordTrace tailWord_7361645 prefixEnd_7361645 3780062292767955263781917 := by
  unfold tailWord_7361645
  simp only [CollatzResearch.WordTrace]
  refine ⟨268501251415024908714822389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179000834276683272476548259 268501251415024908714822389)
  ·
    refine ⟨25171992320158585192014599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268501251415024908714822389 25171992320158585192014599)
    ·
      refine ⟨37757988480237877788021899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25171992320158585192014599 37757988480237877788021899)
      ·
        refine ⟨56636982720356816682032849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37757988480237877788021899 56636982720356816682032849)
        ·
          refine ⟨42477737040267612511524637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56636982720356816682032849 42477737040267612511524637)
          ·
            refine ⟨15929151390100354691821739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42477737040267612511524637 15929151390100354691821739)
            ·
              refine ⟨23893727085150532037732609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15929151390100354691821739 23893727085150532037732609)
              ·
                refine ⟨17920295313862899028299457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23893727085150532037732609 17920295313862899028299457)
                ·
                  refine ⟨13440221485397174271224593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17920295313862899028299457 13440221485397174271224593)
                  ·
                    refine ⟨10080166114047880703418445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13440221485397174271224593 10080166114047880703418445)
                    ·
                      refine ⟨3780062292767955263781917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10080166114047880703418445 3780062292767955263781917)
                      ·
                        rfl

theorem cell23_7361645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_7361645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361645 prefixEnd_7361645 := by exact prefixLift 7361645
  have htrace : WordTrace (prefixWord ++ tailWord_7361645) baseStart_7361645 baseEnd_7361645 := by
    simpa [prefixWord, tailWord_7361645, baseEnd_7361645] using wordTrace_append hprefix tailTrace_7361645
  have hstable : (prefixWord ++ tailWord_7361645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361645).length < 2 ^ (prefixWord ++ tailWord_7361645).sum := by decide
  have hdescent : baseEnd_7361645 < baseStart_7361645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361665 : List Nat := [1, 2, 4, 2, 2, 1, 4, 1, 6]
def baseStart_7361665 : Nat := 118140960795 + 7361665 * 2 ^ 59
def prefixEnd_7361665 : Nat := 4983230072969 + 3 ^ 40 * 7361665 * 2
def baseEnd_7361665 : Nat := 420008062486782798392425

theorem tailTrace_7361665 : CollatzResearch.WordTrace tailWord_7361665 prefixEnd_7361665 420008062486782798392425 := by
  unfold tailWord_7361665
  simp only [CollatzResearch.WordTrace]
  refine ⟨268501980874952452130550449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179001320583301634753700299 268501980874952452130550449)
  ·
    refine ⟨201376485656214339097912837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268501980874952452130550449 201376485656214339097912837)
    ·
      refine ⟨37758091060540188580858657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201376485656214339097912837 37758091060540188580858657)
      ·
        refine ⟨28318568295405141435643993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37758091060540188580858657 28318568295405141435643993)
        ·
          refine ⟨21238926221553856076732995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28318568295405141435643993 21238926221553856076732995)
          ·
            refine ⟨31858389332330784115099493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21238926221553856076732995 31858389332330784115099493)
            ·
              refine ⟨5973447999812022021581155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31858389332330784115099493 5973447999812022021581155)
              ·
                refine ⟨8960171999718033032371733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5973447999812022021581155 8960171999718033032371733)
                ·
                  refine ⟨420008062486782798392425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8960171999718033032371733 420008062486782798392425)
                  ·
                    rfl

theorem cell23_7361665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 6].length) (baseStart_7361665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361665 prefixEnd_7361665 := by exact prefixLift 7361665
  have htrace : WordTrace (prefixWord ++ tailWord_7361665) baseStart_7361665 baseEnd_7361665 := by
    simpa [prefixWord, tailWord_7361665, baseEnd_7361665] using wordTrace_append hprefix tailTrace_7361665
  have hstable : (prefixWord ++ tailWord_7361665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361665).length < 2 ^ (prefixWord ++ tailWord_7361665).sum := by decide
  have hdescent : baseEnd_7361665 < baseStart_7361665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361711 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 6]
def baseStart_7361711 : Nat := 118140960795 + 7361711 * 2 ^ 59
def prefixEnd_7361711 : Nat := 4983230072969 + 3 ^ 40 * 7361711 * 2
def baseEnd_7361711 : Nat := 3780096182491152005556613

theorem tailTrace_7361711 : CollatzResearch.WordTrace tailWord_7361711 prefixEnd_7361711 3780096182491152005556613 := by
  unfold tailWord_7361711
  simp only [CollatzResearch.WordTrace]
  refine ⟨268503658632785801986724987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179002439088523867991149991 268503658632785801986724987)
  ·
    refine ⟨402755487949178702980087481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268503658632785801986724987 402755487949178702980087481)
    ·
      refine ⟨302066615961884027235065611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402755487949178702980087481 302066615961884027235065611)
      ·
        refine ⟨453099923942826040852598417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302066615961884027235065611 453099923942826040852598417)
        ·
          refine ⟨339824942957119530639448813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453099923942826040852598417 339824942957119530639448813)
          ·
            refine ⟨127434353608919823989793305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339824942957119530639448813 127434353608919823989793305)
            ·
              refine ⟨95575765206689867992344979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127434353608919823989793305 95575765206689867992344979)
              ·
                refine ⟨143363647810034801988517469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95575765206689867992344979 143363647810034801988517469)
                ·
                  refine ⟨53761367928763050745694051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143363647810034801988517469 53761367928763050745694051)
                  ·
                    refine ⟨80642051893144576118541077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53761367928763050745694051 80642051893144576118541077)
                    ·
                      refine ⟨3780096182491152005556613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80642051893144576118541077 3780096182491152005556613)
                      ·
                        rfl

theorem cell23_7361711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_7361711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361711 prefixEnd_7361711 := by exact prefixLift 7361711
  have htrace : WordTrace (prefixWord ++ tailWord_7361711) baseStart_7361711 baseEnd_7361711 := by
    simpa [prefixWord, tailWord_7361711, baseEnd_7361711] using wordTrace_append hprefix tailTrace_7361711
  have hstable : (prefixWord ++ tailWord_7361711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361711).length < 2 ^ (prefixWord ++ tailWord_7361711).sum := by decide
  have hdescent : baseEnd_7361711 < baseStart_7361711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361725 : List Nat := [1, 4, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_7361725 : Nat := 118140960795 + 7361725 * 2 ^ 59
def prefixEnd_7361725 : Nat := 4983230072969 + 3 ^ 40 * 7361725 * 2
def baseEnd_7361725 : Nat := 1260034457073438316927183

theorem tailTrace_7361725 : CollatzResearch.WordTrace tailWord_7361725 prefixEnd_7361725 1260034457073438316927183 := by
  unfold tailWord_7361725
  simp only [CollatzResearch.WordTrace]
  refine ⟨268504169254735082377734629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179002779503156721585156419 268504169254735082377734629)
  ·
    refine ⟨50344531735262827945825243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268504169254735082377734629 50344531735262827945825243)
    ·
      refine ⟨75516797602894241918737865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50344531735262827945825243 75516797602894241918737865)
      ·
        refine ⟨56637598202170681439053399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75516797602894241918737865 56637598202170681439053399)
        ·
          refine ⟨84956397303256022158580099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56637598202170681439053399 84956397303256022158580099)
          ·
            refine ⟨127434595954884033237870149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84956397303256022158580099 127434595954884033237870149)
            ·
              refine ⟨23893986741540756232100653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127434595954884033237870149 23893986741540756232100653)
              ·
                refine ⟨8960245028077783587037745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23893986741540756232100653 8960245028077783587037745)
                ·
                  refine ⟨6720183771058337690278309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8960245028077783587037745 6720183771058337690278309)
                  ·
                    refine ⟨1260034457073438316927183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6720183771058337690278309 1260034457073438316927183)
                    ·
                      rfl

theorem cell23_7361725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_7361725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361725 prefixEnd_7361725 := by exact prefixLift 7361725
  have htrace : WordTrace (prefixWord ++ tailWord_7361725) baseStart_7361725 baseEnd_7361725 := by
    simpa [prefixWord, tailWord_7361725, baseEnd_7361725] using wordTrace_append hprefix tailTrace_7361725
  have hstable : (prefixWord ++ tailWord_7361725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361725).length < 2 ^ (prefixWord ++ tailWord_7361725).sum := by decide
  have hdescent : baseEnd_7361725 < baseStart_7361725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361749 : List Nat := [1, 3, 2, 4, 1, 3, 2, 1, 1, 1, 4]
def baseStart_7361749 : Nat := 118140960795 + 7361749 * 2 ^ 59
def prefixEnd_7361749 : Nat := 4983230072969 + 3 ^ 40 * 7361749 * 2
def baseEnd_7361749 : Nat := 3780115694756022856881439

theorem tailTrace_7361749 : CollatzResearch.WordTrace tailWord_7361749 prefixEnd_7361749 3780115694756022856881439 := by
  unfold tailWord_7361749
  simp only [CollatzResearch.WordTrace]
  refine ⟨268505044606648134476608301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179003363071098756317738867 268505044606648134476608301)
  ·
    refine ⟨100689391727493050428728113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268505044606648134476608301 100689391727493050428728113)
    ·
      refine ⟨75517043795619787821546085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100689391727493050428728113 75517043795619787821546085)
      ·
        refine ⟨14159445711678710216539891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75517043795619787821546085 14159445711678710216539891)
        ·
          refine ⟨21239168567518065324809837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14159445711678710216539891 21239168567518065324809837)
          ·
            refine ⟨7964688212819274496803689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21239168567518065324809837 7964688212819274496803689)
            ·
              refine ⟨5973516159614455872602767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7964688212819274496803689 5973516159614455872602767)
              ·
                refine ⟨8960274239421683808904151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5973516159614455872602767 8960274239421683808904151)
                ·
                  refine ⟨13440411359132525713356227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8960274239421683808904151 13440411359132525713356227)
                  ·
                    refine ⟨20160617038698788570034341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13440411359132525713356227 20160617038698788570034341)
                    ·
                      refine ⟨3780115694756022856881439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20160617038698788570034341 3780115694756022856881439)
                      ·
                        rfl

theorem cell23_7361749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_7361749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361749 prefixEnd_7361749 := by exact prefixLift 7361749
  have htrace : WordTrace (prefixWord ++ tailWord_7361749) baseStart_7361749 baseEnd_7361749 := by
    simpa [prefixWord, tailWord_7361749, baseEnd_7361749] using wordTrace_append hprefix tailTrace_7361749
  have hstable : (prefixWord ++ tailWord_7361749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361749).length < 2 ^ (prefixWord ++ tailWord_7361749).sum := by decide
  have hdescent : baseEnd_7361749 < baseStart_7361749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361752 : List Nat := [2, 1, 2, 2, 5, 1, 1, 3, 1, 2, 3]
def baseStart_7361752 : Nat := 118140960795 + 7361752 * 2 ^ 59
def prefixEnd_7361752 : Nat := 4983230072969 + 3 ^ 40 * 7361752 * 2
def baseEnd_7361752 : Nat := 3780117235197986345143925

theorem tailTrace_7361752 : CollatzResearch.WordTrace tailWord_7361752 prefixEnd_7361752 3780117235197986345143925 := by
  unfold tailWord_7361752
  simp only [CollatzResearch.WordTrace]
  refine ⟨134252577012818632994483755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179003436017091510659311673 134252577012818632994483755)
  ·
    refine ⟨201378865519227949491725633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134252577012818632994483755 201378865519227949491725633)
    ·
      refine ⟨151034149139420962118794225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201378865519227949491725633 151034149139420962118794225)
      ·
        refine ⟨113275611854565721589095669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151034149139420962118794225 113275611854565721589095669)
        ·
          refine ⟨10619588611365536398977719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113275611854565721589095669 10619588611365536398977719)
          ·
            refine ⟨15929382917048304598466579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10619588611365536398977719 15929382917048304598466579)
            ·
              refine ⟨23894074375572456897699869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15929382917048304598466579 23894074375572456897699869)
              ·
                refine ⟨8960277890839671336637451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23894074375572456897699869 8960277890839671336637451)
                ·
                  refine ⟨13440416836259507004956177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8960277890839671336637451 13440416836259507004956177)
                  ·
                    refine ⟨10080312627194630253717133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13440416836259507004956177 10080312627194630253717133)
                    ·
                      refine ⟨3780117235197986345143925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10080312627194630253717133 3780117235197986345143925)
                      ·
                        rfl

theorem cell23_7361752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_7361752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361752 prefixEnd_7361752 := by exact prefixLift 7361752
  have htrace : WordTrace (prefixWord ++ tailWord_7361752) baseStart_7361752 baseEnd_7361752 := by
    simpa [prefixWord, tailWord_7361752, baseEnd_7361752] using wordTrace_append hprefix tailTrace_7361752
  have hstable : (prefixWord ++ tailWord_7361752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361752).length < 2 ^ (prefixWord ++ tailWord_7361752).sum := by decide
  have hdescent : baseEnd_7361752 < baseStart_7361752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361879 : List Nat := [1, 1, 3, 2, 3, 4, 2, 2, 5]
def baseStart_7361879 : Nat := 118140960795 + 7361879 * 2 ^ 59
def prefixEnd_7361879 : Nat := 4983230072969 + 3 ^ 40 * 7361879 * 2
def baseEnd_7361879 : Nat := 420020271915678594250649

theorem tailTrace_7361879 : CollatzResearch.WordTrace tailWord_7361879 prefixEnd_7361879 420020271915678594250649 := by
  unfold tailWord_7361879
  simp only [CollatzResearch.WordTrace]
  refine ⟨268509786096177166678840691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179006524064118111119227127 268509786096177166678840691)
  ·
    refine ⟨402764679144265750018261037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268509786096177166678840691 402764679144265750018261037)
    ·
      refine ⟨151036754679099656256847889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402764679144265750018261037 151036754679099656256847889)
      ·
        refine ⟨113277566009324742192635917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151036754679099656256847889 113277566009324742192635917)
        ·
          refine ⟨42479087253496778322238469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113277566009324742192635917 42479087253496778322238469)
          ·
            refine ⟨7964828860030645935419713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42479087253496778322238469 7964828860030645935419713)
            ·
              refine ⟨5973621645022984451564785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7964828860030645935419713 5973621645022984451564785)
              ·
                refine ⟨4480216233767238338673589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5973621645022984451564785 4480216233767238338673589)
                ·
                  refine ⟨420020271915678594250649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4480216233767238338673589 420020271915678594250649)
                  ·
                    rfl

theorem cell23_7361879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 5].length) (baseStart_7361879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361879 prefixEnd_7361879 := by exact prefixLift 7361879
  have htrace : WordTrace (prefixWord ++ tailWord_7361879) baseStart_7361879 baseEnd_7361879 := by
    simpa [prefixWord, tailWord_7361879, baseEnd_7361879] using wordTrace_append hprefix tailTrace_7361879
  have hstable : (prefixWord ++ tailWord_7361879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361879).length < 2 ^ (prefixWord ++ tailWord_7361879).sum := by decide
  have hdescent : baseEnd_7361879 < baseStart_7361879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361905 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 5, 4]
def baseStart_7361905 : Nat := 118140960795 + 7361905 * 2 ^ 59
def prefixEnd_7361905 : Nat := 4983230072969 + 3 ^ 40 * 7361905 * 2
def baseEnd_7361905 : Nat := 1260065265912708082176907

theorem tailTrace_7361905 : CollatzResearch.WordTrace tailWord_7361905 prefixEnd_7361905 1260065265912708082176907 := by
  unfold tailWord_7361905
  simp only [CollatzResearch.WordTrace]
  refine ⟨268510734394082973119287169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179007156262721982079524779 268510734394082973119287169)
  ·
    refine ⟨201383050795562229839465377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268510734394082973119287169 201383050795562229839465377)
    ·
      refine ⟨151037288096671672379599033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201383050795562229839465377 151037288096671672379599033)
      ·
        refine ⟨113277966072503754284699275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151037288096671672379599033 113277966072503754284699275)
        ·
          refine ⟨169916949108755631427048913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113277966072503754284699275 169916949108755631427048913)
          ·
            refine ⟨127437711831566723570286685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169916949108755631427048913 127437711831566723570286685)
            ·
              refine ⟨47789141936837521338857507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127437711831566723570286685 47789141936837521338857507)
              ·
                refine ⟨71683712905256282008286261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47789141936837521338857507 71683712905256282008286261)
                ·
                  refine ⟨6720348084867776438276837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71683712905256282008286261 6720348084867776438276837)
                  ·
                    refine ⟨1260065265912708082176907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6720348084867776438276837 1260065265912708082176907)
                    ·
                      rfl

theorem cell23_7361905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_7361905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361905 prefixEnd_7361905 := by exact prefixLift 7361905
  have htrace : WordTrace (prefixWord ++ tailWord_7361905) baseStart_7361905 baseEnd_7361905 := by
    simpa [prefixWord, tailWord_7361905, baseEnd_7361905] using wordTrace_append hprefix tailTrace_7361905
  have hstable : (prefixWord ++ tailWord_7361905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361905).length < 2 ^ (prefixWord ++ tailWord_7361905).sum := by decide
  have hdescent : baseEnd_7361905 < baseStart_7361905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361909 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 2, 5]
def baseStart_7361909 : Nat := 118140960795 + 7361909 * 2 ^ 59
def prefixEnd_7361909 : Nat := 4983230072969 + 3 ^ 40 * 7361909 * 2
def baseEnd_7361909 : Nat := 1260065950553580743626901

theorem tailTrace_7361909 : CollatzResearch.WordTrace tailWord_7361909 prefixEnd_7361909 1260065950553580743626901 := by
  unfold tailWord_7361909
  simp only [CollatzResearch.WordTrace]
  refine ⟨268510880286068481802432781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179007253524045654534955187 268510880286068481802432781)
  ·
    refine ⟨100691580107275680675912293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268510880286068481802432781 100691580107275680675912293)
    ·
      refine ⟨18879671270114190126733555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100691580107275680675912293 18879671270114190126733555)
      ·
        refine ⟨28319506905171285190100333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18879671270114190126733555 28319506905171285190100333)
        ·
          refine ⟨10619815089439231946287625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28319506905171285190100333 10619815089439231946287625)
          ·
            refine ⟨7964861317079423959715719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10619815089439231946287625 7964861317079423959715719)
            ·
              refine ⟨11947291975619135939573579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7964861317079423959715719 11947291975619135939573579)
              ·
                refine ⟨17920937963428703909360369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11947291975619135939573579 17920937963428703909360369)
                ·
                  refine ⟨13440703472571527932020277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17920937963428703909360369 13440703472571527932020277)
                  ·
                    refine ⟨1260065950553580743626901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13440703472571527932020277 1260065950553580743626901)
                    ·
                      rfl

theorem cell23_7361909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_7361909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361909 prefixEnd_7361909 := by exact prefixLift 7361909
  have htrace : WordTrace (prefixWord ++ tailWord_7361909) baseStart_7361909 baseEnd_7361909 := by
    simpa [prefixWord, tailWord_7361909, baseEnd_7361909] using wordTrace_append hprefix tailTrace_7361909
  have hstable : (prefixWord ++ tailWord_7361909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361909).length < 2 ^ (prefixWord ++ tailWord_7361909).sum := by decide
  have hdescent : baseEnd_7361909 < baseStart_7361909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361915 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 3]
def baseStart_7361915 : Nat := 118140960795 + 7361915 * 2 ^ 59
def prefixEnd_7361915 : Nat := 4983230072969 + 3 ^ 40 * 7361915 * 2
def baseEnd_7361915 : Nat := 3780200932544669207405675

theorem tailTrace_7361915 : CollatzResearch.WordTrace tailWord_7361915 prefixEnd_7361915 3780200932544669207405675 := by
  unfold tailWord_7361915
  simp only [CollatzResearch.WordTrace]
  refine ⟨268511099124046744827151199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179007399416031163218100799 268511099124046744827151199)
  ·
    refine ⟨402766648686070117240726799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268511099124046744827151199 402766648686070117240726799)
    ·
      refine ⟨604149973029105175861090199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402766648686070117240726799 604149973029105175861090199)
      ·
        refine ⟨906224959543657763791635299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604149973029105175861090199 906224959543657763791635299)
        ·
          refine ⟨1359337439315486645687452949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906224959543657763791635299 1359337439315486645687452949)
          ·
            refine ⟨63718942467913436516599357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1359337439315486645687452949 63718942467913436516599357)
            ·
              refine ⟨23894603425467538693724759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63718942467913436516599357 23894603425467538693724759)
              ·
                refine ⟨35841905138201308040587139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23894603425467538693724759 35841905138201308040587139)
                ·
                  refine ⟨53762857707301962060880709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35841905138201308040587139 53762857707301962060880709)
                  ·
                    refine ⟨10080535820119117886415133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53762857707301962060880709 10080535820119117886415133)
                    ·
                      refine ⟨3780200932544669207405675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10080535820119117886415133 3780200932544669207405675)
                      ·
                        rfl

theorem cell23_7361915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 3].length) (baseStart_7361915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361915 prefixEnd_7361915 := by exact prefixLift 7361915
  have htrace : WordTrace (prefixWord ++ tailWord_7361915) baseStart_7361915 baseEnd_7361915 := by
    simpa [prefixWord, tailWord_7361915, baseEnd_7361915] using wordTrace_append hprefix tailTrace_7361915
  have hstable : (prefixWord ++ tailWord_7361915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361915).length < 2 ^ (prefixWord ++ tailWord_7361915).sum := by decide
  have hdescent : baseEnd_7361915 < baseStart_7361915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361952 : List Nat := [2, 1, 1, 4, 1, 2, 5, 1, 6]
def baseStart_7361952 : Nat := 118140960795 + 7361952 * 2 ^ 59
def prefixEnd_7361952 : Nat := 4983230072969 + 3 ^ 40 * 7361952 * 2
def baseEnd_7361952 : Nat := 420024436814320618071445

theorem tailTrace_7361952 : CollatzResearch.WordTrace tailWord_7361952 prefixEnd_7361952 420024436814320618071445 := by
  unfold tailWord_7361952
  simp only [CollatzResearch.WordTrace]
  refine ⟨134256224312456350073124055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179008299083275133430832073 134256224312456350073124055)
  ·
    refine ⟨201384336468684525109686083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134256224312456350073124055 201384336468684525109686083)
    ·
      refine ⟨302076504703026787664529125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201384336468684525109686083 302076504703026787664529125)
      ·
        refine ⟨56639344631817522687099211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302076504703026787664529125 56639344631817522687099211)
        ·
          refine ⟨84959016947726284030648817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56639344631817522687099211 84959016947726284030648817)
          ·
            refine ⟨63719262710794713022986613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84959016947726284030648817 63719262710794713022986613)
            ·
              refine ⟨5973680879137004345904995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63719262710794713022986613 5973680879137004345904995)
              ·
                refine ⟨8960521318705506518857493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5973680879137004345904995 8960521318705506518857493)
                ·
                  refine ⟨420024436814320618071445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8960521318705506518857493 420024436814320618071445)
                  ·
                    rfl

theorem cell23_7361952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 6].length) (baseStart_7361952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361952 prefixEnd_7361952 := by exact prefixLift 7361952
  have htrace : WordTrace (prefixWord ++ tailWord_7361952) baseStart_7361952 baseEnd_7361952 := by
    simpa [prefixWord, tailWord_7361952, baseEnd_7361952] using wordTrace_append hprefix tailTrace_7361952
  have hstable : (prefixWord ++ tailWord_7361952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361952).length < 2 ^ (prefixWord ++ tailWord_7361952).sum := by decide
  have hdescent : baseEnd_7361952 < baseStart_7361952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7361996 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 3, 1, 3]
def baseStart_7361996 : Nat := 118140960795 + 7361996 * 2 ^ 59
def prefixEnd_7361996 : Nat := 4983230072969 + 3 ^ 40 * 7361996 * 2
def baseEnd_7361996 : Nat := 3780242524477683390492803

theorem tailTrace_7361996 : CollatzResearch.WordTrace tailWord_7361996 prefixEnd_7361996 3780242524477683390492803 := by
  unfold tailWord_7361996
  simp only [CollatzResearch.WordTrace]
  refine ⟨134257026718376647830424921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179009368957835530440566561 134257026718376647830424921)
  ·
    refine ⟨100692770038782485872818691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134257026718376647830424921 100692770038782485872818691)
    ·
      refine ⟨151039155058173728809228037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100692770038782485872818691 151039155058173728809228037)
      ·
        refine ⟨28319841573407574151730257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151039155058173728809228037 28319841573407574151730257)
        ·
          refine ⟨21239881180055680613797693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28319841573407574151730257 21239881180055680613797693)
          ·
            refine ⟨7964955442520880230174135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21239881180055680613797693 7964955442520880230174135)
            ·
              refine ⟨11947433163781320345261203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7964955442520880230174135 11947433163781320345261203)
              ·
                refine ⟨17921149745671980517891805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11947433163781320345261203 17921149745671980517891805)
                ·
                  refine ⟨6720431154626992694209427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17921149745671980517891805 6720431154626992694209427)
                  ·
                    refine ⟨10080646731940489041314141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6720431154626992694209427 10080646731940489041314141)
                    ·
                      refine ⟨3780242524477683390492803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10080646731940489041314141 3780242524477683390492803)
                      ·
                        rfl

theorem cell23_7361996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_7361996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7361996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7361996 prefixEnd_7361996 := by exact prefixLift 7361996
  have htrace : WordTrace (prefixWord ++ tailWord_7361996) baseStart_7361996 baseEnd_7361996 := by
    simpa [prefixWord, tailWord_7361996, baseEnd_7361996] using wordTrace_append hprefix tailTrace_7361996
  have hstable : (prefixWord ++ tailWord_7361996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7361996).length < 2 ^ (prefixWord ++ tailWord_7361996).sum := by decide
  have hdescent : baseEnd_7361996 < baseStart_7361996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7361996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362015 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 6]
def baseStart_7362015 : Nat := 118140960795 + 7362015 * 2 ^ 59
def prefixEnd_7362015 : Nat := 4983230072969 + 3 ^ 40 * 7362015 * 2
def baseEnd_7362015 : Nat := 3780252280610118816155215

theorem tailTrace_7362015 : CollatzResearch.WordTrace tailWord_7362015 prefixEnd_7362015 3780252280610118816155215 := by
  unfold tailWord_7362015
  simp only [CollatzResearch.WordTrace]
  refine ⟨268514746423684461905791499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179009830949122974603860999 268514746423684461905791499)
  ·
    refine ⟨402772119635526692858687249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268514746423684461905791499 402772119635526692858687249)
    ·
      refine ⟨302079089726645019644015437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402772119635526692858687249 302079089726645019644015437)
      ·
        refine ⟨113279658647491882366505789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302079089726645019644015437 113279658647491882366505789)
        ·
          refine ⟨42479871992809455887439671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113279658647491882366505789 42479871992809455887439671)
          ·
            refine ⟨63719807989214183831159507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42479871992809455887439671 63719807989214183831159507)
            ·
              refine ⟨95579711983821275746739261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63719807989214183831159507 95579711983821275746739261)
              ·
                refine ⟨35842391993932978405027223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95579711983821275746739261 35842391993932978405027223)
                ·
                  refine ⟨53763587990899467607540835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35842391993932978405027223 53763587990899467607540835)
                  ·
                    refine ⟨80645381986349201411311253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53763587990899467607540835 80645381986349201411311253)
                    ·
                      refine ⟨3780252280610118816155215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80645381986349201411311253 3780252280610118816155215)
                      ·
                        rfl

theorem cell23_7362015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_7362015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362015 prefixEnd_7362015 := by exact prefixLift 7362015
  have htrace : WordTrace (prefixWord ++ tailWord_7362015) baseStart_7362015 baseEnd_7362015 := by
    simpa [prefixWord, tailWord_7362015, baseEnd_7362015] using wordTrace_append hprefix tailTrace_7362015
  have hstable : (prefixWord ++ tailWord_7362015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362015).length < 2 ^ (prefixWord ++ tailWord_7362015).sum := by decide
  have hdescent : baseEnd_7362015 < baseStart_7362015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362019 : List Nat := [1, 1, 1, 6, 2, 1, 3, 2, 1, 1, 4]
def baseStart_7362019 : Nat := 118140960795 + 7362019 * 2 ^ 59
def prefixEnd_7362019 : Nat := 4983230072969 + 3 ^ 40 * 7362019 * 2
def baseEnd_7362019 : Nat := 3780254334532736800505197

theorem tailTrace_7362019 : CollatzResearch.WordTrace tailWord_7362019 prefixEnd_7362019 3780254334532736800505197 := by
  unfold tailWord_7362019
  simp only [CollatzResearch.WordTrace]
  refine ⟨268514892315669970588937111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179009928210446647059291407 268514892315669970588937111)
  ·
    refine ⟨402772338473504955883405667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268514892315669970588937111 402772338473504955883405667)
    ·
      refine ⟨604158507710257433825108501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402772338473504955883405667 604158507710257433825108501)
      ·
        refine ⟨28319930048918317210551961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 604158507710257433825108501 28319930048918317210551961)
        ·
          refine ⟨21239947536688737907913971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28319930048918317210551961 21239947536688737907913971)
          ·
            refine ⟨31859921305033106861870957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21239947536688737907913971 31859921305033106861870957)
            ·
              refine ⟨11947470489387415073201609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31859921305033106861870957 11947470489387415073201609)
              ·
                refine ⟨8960602867040561304901207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11947470489387415073201609 8960602867040561304901207)
                ·
                  refine ⟨13440904300560841957351811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8960602867040561304901207 13440904300560841957351811)
                  ·
                    refine ⟨20161356450841262936027717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13440904300560841957351811 20161356450841262936027717)
                    ·
                      refine ⟨3780254334532736800505197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20161356450841262936027717 3780254334532736800505197)
                      ·
                        rfl

theorem cell23_7362019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_7362019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362019 prefixEnd_7362019 := by exact prefixLift 7362019
  have htrace : WordTrace (prefixWord ++ tailWord_7362019) baseStart_7362019 baseEnd_7362019 := by
    simpa [prefixWord, tailWord_7362019, baseEnd_7362019] using wordTrace_append hprefix tailTrace_7362019
  have hstable : (prefixWord ++ tailWord_7362019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362019).length < 2 ^ (prefixWord ++ tailWord_7362019).sum := by decide
  have hdescent : baseEnd_7362019 < baseStart_7362019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362029 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_7362029 : Nat := 118140960795 + 7362029 * 2 ^ 59
def prefixEnd_7362029 : Nat := 4983230072969 + 3 ^ 40 * 7362029 * 2
def baseEnd_7362029 : Nat := 1260086489779760587126717

theorem tailTrace_7362029 : CollatzResearch.WordTrace tailWord_7362029 prefixEnd_7362029 1260086489779760587126717 := by
  unfold tailWord_7362029
  simp only [CollatzResearch.WordTrace]
  refine ⟨268515257045633742296801141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179010171363755828197867427 268515257045633742296801141)
  ·
    refine ⟨25173305348028163340325107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268515257045633742296801141 25173305348028163340325107)
    ·
      refine ⟨37759958022042245010487661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25173305348028163340325107 37759958022042245010487661)
      ·
        refine ⟨14159984258265841878932873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37759958022042245010487661 14159984258265841878932873)
        ·
          refine ⟨10619988193699381409199655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14159984258265841878932873 10619988193699381409199655)
          ·
            refine ⟨15929982290549072113799483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10619988193699381409199655 15929982290549072113799483)
            ·
              refine ⟨23894973435823608170699225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15929982290549072113799483 23894973435823608170699225)
              ·
                refine ⟨17921230076867706128024419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23894973435823608170699225 17921230076867706128024419)
                ·
                  refine ⟨26881845115301559192036629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17921230076867706128024419 26881845115301559192036629)
                  ·
                    refine ⟨1260086489779760587126717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26881845115301559192036629 1260086489779760587126717)
                    ·
                      rfl

theorem cell23_7362029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_7362029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362029 prefixEnd_7362029 := by exact prefixLift 7362029
  have htrace : WordTrace (prefixWord ++ tailWord_7362029) baseStart_7362029 baseEnd_7362029 := by
    simpa [prefixWord, tailWord_7362029, baseEnd_7362029] using wordTrace_append hprefix tailTrace_7362029
  have hstable : (prefixWord ++ tailWord_7362029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362029).length < 2 ^ (prefixWord ++ tailWord_7362029).sum := by decide
  have hdescent : baseEnd_7362029 < baseStart_7362029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362032 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 4]
def baseStart_7362032 : Nat := 118140960795 + 7362032 * 2 ^ 59
def prefixEnd_7362032 : Nat := 4983230072969 + 3 ^ 40 * 7362032 * 2
def baseEnd_7362032 : Nat := 3780261009781245249642637

theorem tailTrace_7362032 : CollatzResearch.WordTrace tailWord_7362032 prefixEnd_7362032 3780261009781245249642637 := by
  unfold tailWord_7362032
  simp only [CollatzResearch.WordTrace]
  refine ⟨134257683232311436904580175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179010244309748582539440233 134257683232311436904580175)
  ·
    refine ⟨201386524848467155356870263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134257683232311436904580175 201386524848467155356870263)
    ·
      refine ⟨302079787272700733035305395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201386524848467155356870263 302079787272700733035305395)
      ·
        refine ⟨453119680909051099552958093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302079787272700733035305395 453119680909051099552958093)
        ·
          refine ⟨169919880340894162332359285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453119680909051099552958093 169919880340894162332359285)
          ·
            refine ⟨15929988781958827718658683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169919880340894162332359285 15929988781958827718658683)
            ·
              refine ⟨23894983172938241577988025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15929988781958827718658683 23894983172938241577988025)
              ·
                refine ⟨17921237379703681183491019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23894983172938241577988025 17921237379703681183491019)
                ·
                  refine ⟨26881856069555521775236529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17921237379703681183491019 26881856069555521775236529)
                  ·
                    refine ⟨20161392052166641331427397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26881856069555521775236529 20161392052166641331427397)
                    ·
                      refine ⟨3780261009781245249642637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20161392052166641331427397 3780261009781245249642637)
                      ·
                        rfl

theorem cell23_7362032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_7362032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362032 prefixEnd_7362032 := by exact prefixLift 7362032
  have htrace : WordTrace (prefixWord ++ tailWord_7362032) baseStart_7362032 baseEnd_7362032 := by
    simpa [prefixWord, tailWord_7362032, baseEnd_7362032] using wordTrace_append hprefix tailTrace_7362032
  have hstable : (prefixWord ++ tailWord_7362032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362032).length < 2 ^ (prefixWord ++ tailWord_7362032).sum := by decide
  have hdescent : baseEnd_7362032 < baseStart_7362032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362059 : List Nat := [1, 1, 1, 1, 9, 1, 1, 8]
def baseStart_7362059 : Nat := 118140960795 + 7362059 * 2 ^ 59
def prefixEnd_7362059 : Nat := 4983230072969 + 3 ^ 40 * 7362059 * 2
def baseEnd_7362059 : Nat := 140010180509589505333519

theorem tailTrace_7362059 : CollatzResearch.WordTrace tailWord_7362059 prefixEnd_7362059 140010180509589505333519 := by
  unfold tailWord_7362059
  simp only [CollatzResearch.WordTrace]
  refine ⟨268516351235525057420393231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179010900823683371613595487 268516351235525057420393231)
  ·
    refine ⟨402774526853287586130589847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268516351235525057420393231 402774526853287586130589847)
    ·
      refine ⟨604161790279931379195884771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402774526853287586130589847 604161790279931379195884771)
      ·
        refine ⟨906242685419897068793827157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604161790279931379195884771 906242685419897068793827157)
        ·
          refine ⟨5310015734882209387463831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 906242685419897068793827157 5310015734882209387463831)
          ·
            refine ⟨7965023602323314081195747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5310015734882209387463831 7965023602323314081195747)
            ·
              refine ⟨11947535403484971121793621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7965023602323314081195747 11947535403484971121793621)
              ·
                refine ⟨140010180509589505333519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11947535403484971121793621 140010180509589505333519)
                ·
                  rfl

theorem cell23_7362059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 8].length) (baseStart_7362059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362059 prefixEnd_7362059 := by exact prefixLift 7362059
  have htrace : WordTrace (prefixWord ++ tailWord_7362059) baseStart_7362059 baseEnd_7362059 := by
    simpa [prefixWord, tailWord_7362059, baseEnd_7362059] using wordTrace_append hprefix tailTrace_7362059
  have hstable : (prefixWord ++ tailWord_7362059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362059).length < 2 ^ (prefixWord ++ tailWord_7362059).sum := by decide
  have hdescent : baseEnd_7362059 < baseStart_7362059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362069 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_7362069 : Nat := 118140960795 + 7362069 * 2 ^ 59
def prefixEnd_7362069 : Nat := 4983230072969 + 3 ^ 40 * 7362069 * 2
def baseEnd_7362069 : Nat := 3780280008565461604879967

theorem tailTrace_7362069 : CollatzResearch.WordTrace tailWord_7362069 prefixEnd_7362069 3780280008565461604879967 := by
  unfold tailWord_7362069
  simp only [CollatzResearch.WordTrace]
  refine ⟨268516715965488829128257261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179011143976992552752171507 268516715965488829128257261)
  ·
    refine ⟨100693768487058310923096473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268516715965488829128257261 100693768487058310923096473)
    ·
      refine ⟨75520326365293733192322355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100693768487058310923096473 75520326365293733192322355)
      ·
        refine ⟨113280489547940599788483533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75520326365293733192322355 113280489547940599788483533)
        ·
          refine ⟨42480183580477724920681325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113280489547940599788483533 42480183580477724920681325)
          ·
            refine ⟨15930068842679146845255497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42480183580477724920681325 15930068842679146845255497)
            ·
              refine ⟨11947551632009360133941623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15930068842679146845255497 11947551632009360133941623)
              ·
                refine ⟨17921327448014040200912435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11947551632009360133941623 17921327448014040200912435)
                ·
                  refine ⟨26881991172021060301368653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17921327448014040200912435 26881991172021060301368653)
                  ·
                    refine ⟨10080746689507897613013245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26881991172021060301368653 10080746689507897613013245)
                    ·
                      refine ⟨3780280008565461604879967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10080746689507897613013245 3780280008565461604879967)
                      ·
                        rfl

theorem cell23_7362069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_7362069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362069 prefixEnd_7362069 := by exact prefixLift 7362069
  have htrace : WordTrace (prefixWord ++ tailWord_7362069) baseStart_7362069 baseEnd_7362069 := by
    simpa [prefixWord, tailWord_7362069, baseEnd_7362069] using wordTrace_append hprefix tailTrace_7362069
  have hstable : (prefixWord ++ tailWord_7362069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362069).length < 2 ^ (prefixWord ++ tailWord_7362069).sum := by decide
  have hdescent : baseEnd_7362069 < baseStart_7362069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362079 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 3, 3, 2]
def baseStart_7362079 : Nat := 118140960795 + 7362079 * 2 ^ 59
def prefixEnd_7362079 : Nat := 4983230072969 + 3 ^ 40 * 7362079 * 2
def baseEnd_7362079 : Nat := 3780285143372006565754921

theorem tailTrace_7362079 : CollatzResearch.WordTrace tailWord_7362079 prefixEnd_7362079 3780285143372006565754921 := by
  unfold tailWord_7362079
  simp only [CollatzResearch.WordTrace]
  refine ⟨268517080695452600836121291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179011387130301733890747527 268517080695452600836121291)
  ·
    refine ⟨402775621043178901254181937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268517080695452600836121291 402775621043178901254181937)
    ·
      refine ⟨302081715782384175940636453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402775621043178901254181937 302081715782384175940636453)
      ·
        refine ⟨56640321709197032988869335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302081715782384175940636453 56640321709197032988869335)
        ·
          refine ⟨84960482563795549483304003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56640321709197032988869335 84960482563795549483304003)
          ·
            refine ⟨127440723845693324224956005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84960482563795549483304003 127440723845693324224956005)
            ·
              refine ⟨23895135721067498292179251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127440723845693324224956005 23895135721067498292179251)
              ·
                refine ⟨35842703581601247438268877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23895135721067498292179251 35842703581601247438268877)
                ·
                  refine ⟨13441013843100467789350829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35842703581601247438268877 13441013843100467789350829)
                  ·
                    refine ⟨5040380191162675421006561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13441013843100467789350829 5040380191162675421006561)
                    ·
                      refine ⟨3780285143372006565754921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5040380191162675421006561 3780285143372006565754921)
                      ·
                        rfl

theorem cell23_7362079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_7362079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362079 prefixEnd_7362079 := by exact prefixLift 7362079
  have htrace : WordTrace (prefixWord ++ tailWord_7362079) baseStart_7362079 baseEnd_7362079 := by
    simpa [prefixWord, tailWord_7362079, baseEnd_7362079] using wordTrace_append hprefix tailTrace_7362079
  have hstable : (prefixWord ++ tailWord_7362079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362079).length < 2 ^ (prefixWord ++ tailWord_7362079).sum := by decide
  have hdescent : baseEnd_7362079 < baseStart_7362079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362085 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 3, 8]
def baseStart_7362085 : Nat := 118140960795 + 7362085 * 2 ^ 59
def prefixEnd_7362085 : Nat := 4983230072969 + 3 ^ 40 * 7362085 * 2
def baseEnd_7362085 : Nat := 1260096074751977847426631

theorem tailTrace_7362085 : CollatzResearch.WordTrace tailWord_7362085 prefixEnd_7362085 1260096074751977847426631 := by
  unfold tailWord_7362085
  simp only [CollatzResearch.WordTrace]
  refine ⟨268517299533430863860839709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179011533022287242573893139 268517299533430863860839709)
  ·
    refine ⟨100693987325036573947814891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268517299533430863860839709 100693987325036573947814891)
    ·
      refine ⟨151040980987554860921722337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100693987325036573947814891 151040980987554860921722337)
      ·
        refine ⟨113280735740666145691291753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151040980987554860921722337 113280735740666145691291753)
        ·
          refine ⟨84960551805499609268468815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113280735740666145691291753 84960551805499609268468815)
          ·
            refine ⟨127440827708249413902703223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84960551805499609268468815 127440827708249413902703223)
            ·
              refine ⟨191161241562374120854054835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127440827708249413902703223 191161241562374120854054835)
              ·
                refine ⟨286741862343561181281082253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191161241562374120854054835 286741862343561181281082253)
                ·
                  refine ⟨107528198378835442980405845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286741862343561181281082253 107528198378835442980405845)
                  ·
                    refine ⟨1260096074751977847426631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107528198378835442980405845 1260096074751977847426631)
                    ·
                      rfl

theorem cell23_7362085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_7362085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362085 prefixEnd_7362085 := by exact prefixLift 7362085
  have htrace : WordTrace (prefixWord ++ tailWord_7362085) baseStart_7362085 baseEnd_7362085 := by
    simpa [prefixWord, tailWord_7362085, baseEnd_7362085] using wordTrace_append hprefix tailTrace_7362085
  have hstable : (prefixWord ++ tailWord_7362085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362085).length < 2 ^ (prefixWord ++ tailWord_7362085).sum := by decide
  have hdescent : baseEnd_7362085 < baseStart_7362085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362122 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_7362122 : Nat := 118140960795 + 7362122 * 2 ^ 59
def prefixEnd_7362122 : Nat := 4983230072969 + 3 ^ 40 * 7362122 * 2
def baseEnd_7362122 : Nat := 3780307223040149897517223

theorem tailTrace_7362122 : CollatzResearch.WordTrace tailWord_7362122 prefixEnd_7362122 3780307223040149897517223 := by
  unfold tailWord_7362122
  simp only [CollatzResearch.WordTrace]
  refine ⟨67129662258574204794984155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179012432689531212786624413 67129662258574204794984155)
  ·
    refine ⟨100694493387861307192476233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67129662258574204794984155 100694493387861307192476233)
    ·
      refine ⟨75520870040895980394357175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100694493387861307192476233 75520870040895980394357175)
      ·
        refine ⟨113281305061343970591535763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75520870040895980394357175 113281305061343970591535763)
        ·
          refine ⟨169921957592015955887303645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113281305061343970591535763 169921957592015955887303645)
          ·
            refine ⟨63720734097005983457738867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169921957592015955887303645 63720734097005983457738867)
            ·
              refine ⟨95581101145508975186608301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63720734097005983457738867 95581101145508975186608301)
              ·
                refine ⟨35842912929565865694978113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95581101145508975186608301 35842912929565865694978113)
                ·
                  refine ⟨26882184697174399271233585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35842912929565865694978113 26882184697174399271233585)
                  ·
                    refine ⟨20161638522880799453425189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26882184697174399271233585 20161638522880799453425189)
                    ·
                      refine ⟨3780307223040149897517223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20161638522880799453425189 3780307223040149897517223)
                      ·
                        rfl

theorem cell23_7362122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_7362122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362122 prefixEnd_7362122 := by exact prefixLift 7362122
  have htrace : WordTrace (prefixWord ++ tailWord_7362122) baseStart_7362122 baseEnd_7362122 := by
    simpa [prefixWord, tailWord_7362122, baseEnd_7362122] using wordTrace_append hprefix tailTrace_7362122
  have hstable : (prefixWord ++ tailWord_7362122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362122).length < 2 ^ (prefixWord ++ tailWord_7362122).sum := by decide
  have hdescent : baseEnd_7362122 < baseStart_7362122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362132 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 7]
def baseStart_7362132 : Nat := 118140960795 + 7362132 * 2 ^ 59
def prefixEnd_7362132 : Nat := 4983230072969 + 3 ^ 40 * 7362132 * 2
def baseEnd_7362132 : Nat := 420034706427410539821353

theorem tailTrace_7362132 : CollatzResearch.WordTrace tailWord_7362132 prefixEnd_7362132 420034706427410539821353 := by
  unfold tailWord_7362132
  simp only [CollatzResearch.WordTrace]
  refine ⟨134259506882130295443900325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179012675842840393925200433 134259506882130295443900325)
  ·
    refine ⟨25173657540399430395731311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134259506882130295443900325 25173657540399430395731311)
    ·
      refine ⟨37760486310599145593596967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25173657540399430395731311 37760486310599145593596967)
      ·
        refine ⟨56640729465898718390395451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37760486310599145593596967 56640729465898718390395451)
        ·
          refine ⟨84961094198848077585593177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56640729465898718390395451 84961094198848077585593177)
          ·
            refine ⟨63720820649136058189194883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84961094198848077585593177 63720820649136058189194883)
            ·
              refine ⟨95581230973704087283792325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63720820649136058189194883 95581230973704087283792325)
              ·
                refine ⟨17921480807569516365711061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95581230973704087283792325 17921480807569516365711061)
                ·
                  refine ⟨420034706427410539821353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17921480807569516365711061 420034706427410539821353)
                  ·
                    rfl

theorem cell23_7362132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_7362132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362132 prefixEnd_7362132 := by exact prefixLift 7362132
  have htrace : WordTrace (prefixWord ++ tailWord_7362132) baseStart_7362132 baseEnd_7362132 := by
    simpa [prefixWord, tailWord_7362132, baseEnd_7362132] using wordTrace_append hprefix tailTrace_7362132
  have hstable : (prefixWord ++ tailWord_7362132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362132).length < 2 ^ (prefixWord ++ tailWord_7362132).sum := by decide
  have hdescent : baseEnd_7362132 < baseStart_7362132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362166 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_7362166 : Nat := 118140960795 + 7362166 * 2 ^ 59
def prefixEnd_7362166 : Nat := 4983230072969 + 3 ^ 40 * 7362166 * 2
def baseEnd_7362166 : Nat := 420036646243216413929669

theorem tailTrace_7362166 : CollatzResearch.WordTrace tailWord_7362166 prefixEnd_7362166 420036646243216413929669 := by
  unfold tailWord_7362166
  simp only [CollatzResearch.WordTrace]
  refine ⟨16782515865383588418408647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179013502564091609796358901 16782515865383588418408647)
  ·
    refine ⟨25173773798075382627612971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16782515865383588418408647 25173773798075382627612971)
    ·
      refine ⟨37760660697113073941419457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25173773798075382627612971 37760660697113073941419457)
      ·
        refine ⟨28320495522834805456064593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37760660697113073941419457 28320495522834805456064593)
        ·
          refine ⟨21240371642126104092048445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28320495522834805456064593 21240371642126104092048445)
          ·
            refine ⟨7965139365797289034518167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21240371642126104092048445 7965139365797289034518167)
            ·
              refine ⟨11947709048695933551777251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7965139365797289034518167 11947709048695933551777251)
              ·
                refine ⟨17921563573043900327665877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11947709048695933551777251 17921563573043900327665877)
                ·
                  refine ⟨420036646243216413929669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17921563573043900327665877 420036646243216413929669)
                  ·
                    rfl

theorem cell23_7362166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_7362166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362166 prefixEnd_7362166 := by exact prefixLift 7362166
  have htrace : WordTrace (prefixWord ++ tailWord_7362166) baseStart_7362166 baseEnd_7362166 := by
    simpa [prefixWord, tailWord_7362166, baseEnd_7362166] using wordTrace_append hprefix tailTrace_7362166
  have hstable : (prefixWord ++ tailWord_7362166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362166).length < 2 ^ (prefixWord ++ tailWord_7362166).sum := by decide
  have hdescent : baseEnd_7362166 < baseStart_7362166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362169 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 2, 5, 2]
def baseStart_7362169 : Nat := 118140960795 + 7362169 * 2 ^ 59
def prefixEnd_7362169 : Nat := 4983230072969 + 3 ^ 40 * 7362169 * 2
def baseEnd_7362169 : Nat := 3780331356630911213629507

theorem tailTrace_7362169 : CollatzResearch.WordTrace tailWord_7362169 prefixEnd_7362169 3780331356630911213629507 := by
  unfold tailWord_7362169
  simp only [CollatzResearch.WordTrace]
  refine ⟨268520363265126546206897561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179013575510084364137931707 268520363265126546206897561)
  ·
    refine ⟨201390272448844909655173171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268520363265126546206897561 201390272448844909655173171)
    ·
      refine ⟨302085408673267364482759757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201390272448844909655173171 302085408673267364482759757)
      ·
        refine ⟨113282028252475261681034909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302085408673267364482759757 113282028252475261681034909)
        ·
          refine ⟨42480760594678223130388091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113282028252475261681034909 42480760594678223130388091)
          ·
            refine ⟨63721140892017334695582137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42480760594678223130388091 63721140892017334695582137)
            ·
              refine ⟨47790855669013001021686603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63721140892017334695582137 47790855669013001021686603)
              ·
                refine ⟨71686283503519501532529905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47790855669013001021686603 71686283503519501532529905)
                ·
                  refine ⟨53764712627639626149397429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71686283503519501532529905 53764712627639626149397429)
                  ·
                    refine ⟨5040441808841214951506009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53764712627639626149397429 5040441808841214951506009)
                    ·
                      refine ⟨3780331356630911213629507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5040441808841214951506009 3780331356630911213629507)
                      ·
                        rfl

theorem cell23_7362169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_7362169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362169 prefixEnd_7362169 := by exact prefixLift 7362169
  have htrace : WordTrace (prefixWord ++ tailWord_7362169) baseStart_7362169 baseEnd_7362169 := by
    simpa [prefixWord, tailWord_7362169, baseEnd_7362169] using wordTrace_append hprefix tailTrace_7362169
  have hstable : (prefixWord ++ tailWord_7362169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362169).length < 2 ^ (prefixWord ++ tailWord_7362169).sum := by decide
  have hdescent : baseEnd_7362169 < baseStart_7362169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362199 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 4]
def baseStart_7362199 : Nat := 118140960795 + 7362199 * 2 ^ 59
def prefixEnd_7362199 : Nat := 4983230072969 + 3 ^ 40 * 7362199 * 2
def baseEnd_7362199 : Nat := 3780346761050546096254369

theorem tailTrace_7362199 : CollatzResearch.WordTrace tailWord_7362199 prefixEnd_7362199 3780346761050546096254369 := by
  unfold tailWord_7362199
  simp only [CollatzResearch.WordTrace]
  refine ⟨268521457455017861330489651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179014304970011907553659767 268521457455017861330489651)
  ·
    refine ⟨402782186182526791995734477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268521457455017861330489651 402782186182526791995734477)
    ·
      refine ⟨151043319818447546998400429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402782186182526791995734477 151043319818447546998400429)
      ·
        refine ⟨56641244931917830124400161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151043319818447546998400429 56641244931917830124400161)
        ·
          refine ⟨42480933698938372593300121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56641244931917830124400161 42480933698938372593300121)
          ·
            refine ⟨31860700274203779444975091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42480933698938372593300121 31860700274203779444975091)
            ·
              refine ⟨47791050411305669167462637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31860700274203779444975091 47791050411305669167462637)
              ·
                refine ⟨17921643904239625937798489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47791050411305669167462637 17921643904239625937798489)
                ·
                  refine ⟨13441232928179719453348867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17921643904239625937798489 13441232928179719453348867)
                  ·
                    refine ⟨20161849392269579180023301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13441232928179719453348867 20161849392269579180023301)
                    ·
                      refine ⟨3780346761050546096254369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20161849392269579180023301 3780346761050546096254369)
                      ·
                        rfl

theorem cell23_7362199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_7362199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362199 prefixEnd_7362199 := by exact prefixLift 7362199
  have htrace : WordTrace (prefixWord ++ tailWord_7362199) baseStart_7362199 baseEnd_7362199 := by
    simpa [prefixWord, tailWord_7362199, baseEnd_7362199] using wordTrace_append hprefix tailTrace_7362199
  have hstable : (prefixWord ++ tailWord_7362199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362199).length < 2 ^ (prefixWord ++ tailWord_7362199).sum := by decide
  have hdescent : baseEnd_7362199 < baseStart_7362199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362253 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_7362253 : Nat := 118140960795 + 7362253 * 2 ^ 59
def prefixEnd_7362253 : Nat := 4983230072969 + 3 ^ 40 * 7362253 * 2
def baseEnd_7362253 : Nat := 3780374489005888884979121

theorem tailTrace_7362253 : CollatzResearch.WordTrace tailWord_7362253 prefixEnd_7362253 3780374489005888884979121 := by
  unfold tailWord_7362253
  simp only [CollatzResearch.WordTrace]
  refine ⟨268523426996822228552955413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179015617997881485701970275 268523426996822228552955413)
  ·
    refine ⟨12587035640476041963419785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 268523426996822228552955413 12587035640476041963419785)
    ·
      refine ⟨9440276730357031472564839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12587035640476041963419785 9440276730357031472564839)
      ·
        refine ⟨14160415095535547208847259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9440276730357031472564839 14160415095535547208847259)
        ·
          refine ⟨21240622643303320813270889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14160415095535547208847259 21240622643303320813270889)
          ·
            refine ⟨15930466982477490609953167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21240622643303320813270889 15930466982477490609953167)
            ·
              refine ⟨23895700473716235914929751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15930466982477490609953167 23895700473716235914929751)
              ·
                refine ⟨35843550710574353872394627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23895700473716235914929751 35843550710574353872394627)
                ·
                  refine ⟨53765326065861530808591941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35843550710574353872394627 53765326065861530808591941)
                  ·
                    refine ⟨10080998637349037026610989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53765326065861530808591941 10080998637349037026610989)
                    ·
                      refine ⟨3780374489005888884979121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10080998637349037026610989 3780374489005888884979121)
                      ·
                        rfl

theorem cell23_7362253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_7362253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362253 prefixEnd_7362253 := by exact prefixLift 7362253
  have htrace : WordTrace (prefixWord ++ tailWord_7362253) baseStart_7362253 baseEnd_7362253 := by
    simpa [prefixWord, tailWord_7362253, baseEnd_7362253] using wordTrace_append hprefix tailTrace_7362253
  have hstable : (prefixWord ++ tailWord_7362253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362253).length < 2 ^ (prefixWord ++ tailWord_7362253).sum := by decide
  have hdescent : baseEnd_7362253 < baseStart_7362253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362260 : List Nat := [2, 4, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_7362260 : Nat := 118140960795 + 7362260 * 2 ^ 59
def prefixEnd_7362260 : Nat := 4983230072969 + 3 ^ 40 * 7362260 * 2
def baseEnd_7362260 : Nat := 1260126027790156785863863

theorem tailTrace_7362260 : CollatzResearch.WordTrace tailWord_7362260 prefixEnd_7362260 1260126027790156785863863 := by
  unfold tailWord_7362260
  simp only [CollatzResearch.WordTrace]
  refine ⟨134261841153898434374230117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179015788205197912498973489 134261841153898434374230117)
  ·
    refine ⟨25174095216355956445168147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134261841153898434374230117 25174095216355956445168147)
    ·
      refine ⟨37761142824533934667752221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25174095216355956445168147 37761142824533934667752221)
      ·
        refine ⟨14160428559200225500407083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37761142824533934667752221 14160428559200225500407083)
        ·
          refine ⟨21240642838800338250610625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14160428559200225500407083 21240642838800338250610625)
          ·
            refine ⟨15930482129100253687957969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21240642838800338250610625 15930482129100253687957969)
            ·
              refine ⟨11947861596825190265968477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15930482129100253687957969 11947861596825190265968477)
              ·
                refine ⟨4480448098809446349738179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11947861596825190265968477 4480448098809446349738179)
                ·
                  refine ⟨6720672148214169524607269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480448098809446349738179 6720672148214169524607269)
                  ·
                    refine ⟨1260126027790156785863863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6720672148214169524607269 1260126027790156785863863)
                    ·
                      rfl

theorem cell23_7362260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_7362260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362260 prefixEnd_7362260 := by exact prefixLift 7362260
  have htrace : WordTrace (prefixWord ++ tailWord_7362260) baseStart_7362260 baseEnd_7362260 := by
    simpa [prefixWord, tailWord_7362260, baseEnd_7362260] using wordTrace_append hprefix tailTrace_7362260
  have hstable : (prefixWord ++ tailWord_7362260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362260).length < 2 ^ (prefixWord ++ tailWord_7362260).sum := by decide
  have hdescent : baseEnd_7362260 < baseStart_7362260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362273 : List Nat := [1, 2, 3, 1, 6, 1, 1, 2, 6]
def baseStart_7362273 : Nat := 118140960795 + 7362273 * 2 ^ 59
def prefixEnd_7362273 : Nat := 4983230072969 + 3 ^ 40 * 7362273 * 2
def baseEnd_7362273 : Nat := 420042750957664311858781

theorem tailTrace_7362273 : CollatzResearch.WordTrace tailWord_7362273 prefixEnd_7362273 420042750957664311858781 := by
  unfold tailWord_7362273
  simp only [CollatzResearch.WordTrace]
  refine ⟨268524156456749771968683473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179016104304499847979122315 268524156456749771968683473)
  ·
    refine ⟨201393117342562328976512605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268524156456749771968683473 201393117342562328976512605)
    ·
      refine ⟨75522419003460873366192227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201393117342562328976512605 75522419003460873366192227)
      ·
        refine ⟨113283628505191310049288341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75522419003460873366192227 113283628505191310049288341)
        ·
          refine ⟨5310170086180842658560391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113283628505191310049288341 5310170086180842658560391)
          ·
            refine ⟨7965255129271263987840587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5310170086180842658560391 7965255129271263987840587)
            ·
              refine ⟨11947882693906895981760881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7965255129271263987840587 11947882693906895981760881)
              ·
                refine ⟨8960912020430171986320661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11947882693906895981760881 8960912020430171986320661)
                ·
                  refine ⟨420042750957664311858781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8960912020430171986320661 420042750957664311858781)
                  ·
                    rfl

theorem cell23_7362273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 6].length) (baseStart_7362273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362273 prefixEnd_7362273 := by exact prefixLift 7362273
  have htrace : WordTrace (prefixWord ++ tailWord_7362273) baseStart_7362273 baseEnd_7362273 := by
    simpa [prefixWord, tailWord_7362273, baseEnd_7362273] using wordTrace_append hprefix tailTrace_7362273
  have hstable : (prefixWord ++ tailWord_7362273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362273).length < 2 ^ (prefixWord ++ tailWord_7362273).sum := by decide
  have hdescent : baseEnd_7362273 < baseStart_7362273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362276 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 4, 3, 2]
def baseStart_7362276 : Nat := 118140960795 + 7362276 * 2 ^ 59
def prefixEnd_7362276 : Nat := 4983230072969 + 3 ^ 40 * 7362276 * 2
def baseEnd_7362276 : Nat := 3780386299060942294991515

theorem tailTrace_7362276 : CollatzResearch.WordTrace tailWord_7362276 prefixEnd_7362276 3780386299060942294991515 := by
  unfold tailWord_7362276
  simp only [CollatzResearch.WordTrace]
  refine ⟨134262132937869451740521341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179016177250492602320695121 134262132937869451740521341)
  ·
    refine ⟨50348299851701044402695503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134262132937869451740521341 50348299851701044402695503)
    ·
      refine ⟨75522449777551566604043255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50348299851701044402695503 75522449777551566604043255)
      ·
        refine ⟨113283674666327349906064883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75522449777551566604043255 113283674666327349906064883)
        ·
          refine ⟨169925511999491024859097325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113283674666327349906064883 169925511999491024859097325)
          ·
            refine ⟨63722066999809134322161497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169925511999491024859097325 63722066999809134322161497)
            ·
              refine ⟨47791550249856850741621123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63722066999809134322161497 47791550249856850741621123)
              ·
                refine ⟨71687325374785276112431685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47791550249856850741621123 71687325374785276112431685)
                ·
                  refine ⟨13441373507772239271080941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71687325374785276112431685 13441373507772239271080941)
                  ·
                    refine ⟨5040515065414589726655353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13441373507772239271080941 5040515065414589726655353)
                    ·
                      refine ⟨3780386299060942294991515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5040515065414589726655353 3780386299060942294991515)
                      ·
                        rfl

theorem cell23_7362276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_7362276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362276 prefixEnd_7362276 := by exact prefixLift 7362276
  have htrace : WordTrace (prefixWord ++ tailWord_7362276) baseStart_7362276 baseEnd_7362276 := by
    simpa [prefixWord, tailWord_7362276, baseEnd_7362276] using wordTrace_append hprefix tailTrace_7362276
  have hstable : (prefixWord ++ tailWord_7362276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362276).length < 2 ^ (prefixWord ++ tailWord_7362276).sum := by decide
  have hdescent : baseEnd_7362276 < baseStart_7362276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362283 : List Nat := [1, 1, 1, 1, 2, 4, 4, 4, 1, 1, 3]
def baseStart_7362283 : Nat := 118140960795 + 7362283 * 2 ^ 59
def prefixEnd_7362283 : Nat := 4983230072969 + 3 ^ 40 * 7362283 * 2
def baseEnd_7362283 : Nat := 3780389893425523767603983

theorem tailTrace_7362283 : CollatzResearch.WordTrace tailWord_7362283 prefixEnd_7362283 3780389893425523767603983 := by
  unfold tailWord_7362283
  simp only [CollatzResearch.WordTrace]
  refine ⟨268524521186713543676547503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179016347457809029117698335 268524521186713543676547503)
  ·
    refine ⟨402786781780070315514821255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268524521186713543676547503 402786781780070315514821255)
    ·
      refine ⟨604180172670105473272231883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402786781780070315514821255 604180172670105473272231883)
      ·
        refine ⟨906270259005158209908347825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604180172670105473272231883 906270259005158209908347825)
        ·
          refine ⟨679702694253868657431260869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906270259005158209908347825 679702694253868657431260869)
          ·
            refine ⟨127444255172600373268361413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 679702694253868657431260869 127444255172600373268361413)
            ·
              refine ⟨23895797844862569987817765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127444255172600373268361413 23895797844862569987817765)
              ·
                refine ⟨4480462095911731872715831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23895797844862569987817765 4480462095911731872715831)
                ·
                  refine ⟨6720693143867597809073747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480462095911731872715831 6720693143867597809073747)
                  ·
                    refine ⟨10081039715801396713610621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6720693143867597809073747 10081039715801396713610621)
                    ·
                      refine ⟨3780389893425523767603983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10081039715801396713610621 3780389893425523767603983)
                      ·
                        rfl

theorem cell23_7362283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 1, 1, 3].length) (baseStart_7362283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362283 prefixEnd_7362283 := by exact prefixLift 7362283
  have htrace : WordTrace (prefixWord ++ tailWord_7362283) baseStart_7362283 baseEnd_7362283 := by
    simpa [prefixWord, tailWord_7362283, baseEnd_7362283] using wordTrace_append hprefix tailTrace_7362283
  have hstable : (prefixWord ++ tailWord_7362283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362283).length < 2 ^ (prefixWord ++ tailWord_7362283).sum := by decide
  have hdescent : baseEnd_7362283 < baseStart_7362283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362334 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7362334 : Nat := 118140960795 + 7362334 * 2 ^ 59
def prefixEnd_7362334 : Nat := 4983230072969 + 3 ^ 40 * 7362334 * 2
def baseEnd_7362334 : Nat := 3780416080938903068066249

theorem tailTrace_7362334 : CollatzResearch.WordTrace tailWord_7362334 prefixEnd_7362334 3780416080938903068066249 := by
  unfold tailWord_7362334
  simp only [CollatzResearch.WordTrace]
  refine ⟨33565797663691097423331757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179017587539685852924436037 33565797663691097423331757)
  ·
    refine ⟨12587174123884161533749409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33565797663691097423331757 12587174123884161533749409)
    ·
      refine ⟨9440380592913121150312057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12587174123884161533749409 9440380592913121150312057)
      ·
        refine ⟨7080285444684840862734043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9440380592913121150312057 7080285444684840862734043)
        ·
          refine ⟨10620428167027261294101065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7080285444684840862734043 10620428167027261294101065)
          ·
            refine ⟨7965321125270445970575799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10620428167027261294101065 7965321125270445970575799)
            ·
              refine ⟨11947981687905668955863699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7965321125270445970575799 11947981687905668955863699)
              ·
                refine ⟨17921972531858503433795549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11947981687905668955863699 17921972531858503433795549)
                ·
                  refine ⟨6720739699446938787673331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17921972531858503433795549 6720739699446938787673331)
                  ·
                    refine ⟨10081109549170408181509997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6720739699446938787673331 10081109549170408181509997)
                    ·
                      refine ⟨3780416080938903068066249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10081109549170408181509997 3780416080938903068066249)
                      ·
                        rfl

theorem cell23_7362334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7362334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362334 prefixEnd_7362334 := by exact prefixLift 7362334
  have htrace : WordTrace (prefixWord ++ tailWord_7362334) baseStart_7362334 baseEnd_7362334 := by
    simpa [prefixWord, tailWord_7362334, baseEnd_7362334] using wordTrace_append hprefix tailTrace_7362334
  have hstable : (prefixWord ++ tailWord_7362334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362334).length < 2 ^ (prefixWord ++ tailWord_7362334).sum := by decide
  have hdescent : baseEnd_7362334 < baseStart_7362334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362340 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 3, 2, 2]
def baseStart_7362340 : Nat := 118140960795 + 7362340 * 2 ^ 59
def prefixEnd_7362340 : Nat := 4983230072969 + 3 ^ 40 * 7362340 * 2
def baseEnd_7362340 : Nat := 3780419161822830044591221

theorem tailTrace_7362340 : CollatzResearch.WordTrace tailWord_7362340 prefixEnd_7362340 3780419161822830044591221 := by
  unfold tailWord_7362340
  simp only [CollatzResearch.WordTrace]
  refine ⟨134263300073753521205686237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179017733431671361607581649 134263300073753521205686237)
  ·
    refine ⟨50348737527657570452132339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134263300073753521205686237 50348737527657570452132339)
    ·
      refine ⟨75523106291486355678198509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50348737527657570452132339 75523106291486355678198509)
      ·
        refine ⟨28321164859307383379324441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75523106291486355678198509 28321164859307383379324441)
        ·
          refine ⟨21240873644480537534493331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28321164859307383379324441 21240873644480537534493331)
          ·
            refine ⟨31861310466720806301739997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21240873644480537534493331 31861310466720806301739997)
            ·
              refine ⟨11947991425020302363152499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31861310466720806301739997 11947991425020302363152499)
              ·
                refine ⟨17921987137530453544728749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11947991425020302363152499 17921987137530453544728749)
                ·
                  refine ⟨6720745176573920079273281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17921987137530453544728749 6720745176573920079273281)
                  ·
                    refine ⟨5040558882430440059454961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6720745176573920079273281 5040558882430440059454961)
                    ·
                      refine ⟨3780419161822830044591221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5040558882430440059454961 3780419161822830044591221)
                      ·
                        rfl

theorem cell23_7362340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_7362340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362340 prefixEnd_7362340 := by exact prefixLift 7362340
  have htrace : WordTrace (prefixWord ++ tailWord_7362340) baseStart_7362340 baseEnd_7362340 := by
    simpa [prefixWord, tailWord_7362340, baseEnd_7362340] using wordTrace_append hprefix tailTrace_7362340
  have hstable : (prefixWord ++ tailWord_7362340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362340).length < 2 ^ (prefixWord ++ tailWord_7362340).sum := by decide
  have hdescent : baseEnd_7362340 < baseStart_7362340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362350 : List Nat := [4, 1, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_7362350 : Nat := 118140960795 + 7362350 * 2 ^ 59
def prefixEnd_7362350 : Nat := 4983230072969 + 3 ^ 40 * 7362350 * 2
def baseEnd_7362350 : Nat := 1260141432209791668488725

theorem tailTrace_7362350 : CollatzResearch.WordTrace tailWord_7362350 prefixEnd_7362350 1260141432209791668488725 := by
  unfold tailWord_7362350
  simp only [CollatzResearch.WordTrace]
  refine ⟨33565870609683851764904563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179017976584980542746157669 33565870609683851764904563)
  ·
    refine ⟨50348805914525777647356845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33565870609683851764904563 50348805914525777647356845)
    ·
      refine ⟨18880802217947166617758817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50348805914525777647356845 18880802217947166617758817)
      ·
        refine ⟨14160601663460374963319113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18880802217947166617758817 14160601663460374963319113)
        ·
          refine ⟨10620451247595281222489335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14160601663460374963319113 10620451247595281222489335)
          ·
            refine ⟨15930676871392921833734003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10620451247595281222489335 15930676871392921833734003)
            ·
              refine ⟨23896015307089382750601005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15930676871392921833734003 23896015307089382750601005)
              ·
                refine ⟨8961005740158518531475377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23896015307089382750601005 8961005740158518531475377)
                ·
                  refine ⟨6720754305118888898606533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8961005740158518531475377 6720754305118888898606533)
                  ·
                    refine ⟨1260141432209791668488725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6720754305118888898606533 1260141432209791668488725)
                    ·
                      rfl

theorem cell23_7362350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_7362350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362350 prefixEnd_7362350 := by exact prefixLift 7362350
  have htrace : WordTrace (prefixWord ++ tailWord_7362350) baseStart_7362350 baseEnd_7362350 := by
    simpa [prefixWord, tailWord_7362350, baseEnd_7362350] using wordTrace_append hprefix tailTrace_7362350
  have hstable : (prefixWord ++ tailWord_7362350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362350).length < 2 ^ (prefixWord ++ tailWord_7362350).sum := by decide
  have hdescent : baseEnd_7362350 < baseStart_7362350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362391 : List Nat := [1, 1, 3, 2, 6, 1, 2, 2, 1, 2, 2]
def baseStart_7362391 : Nat := 118140960795 + 7362391 * 2 ^ 59
def prefixEnd_7362391 : Nat := 4983230072969 + 3 ^ 40 * 7362391 * 2
def baseEnd_7362391 : Nat := 3780445349336209345053487

theorem tailTrace_7362391 : CollatzResearch.WordTrace tailWord_7362391 prefixEnd_7362391 3780445349336209345053487 := by
  unfold tailWord_7362391
  simp only [CollatzResearch.WordTrace]
  refine ⟨268528460270322278121479027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179018973513548185414319351 268528460270322278121479027)
  ·
    refine ⟨402792690405483417182218541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268528460270322278121479027 402792690405483417182218541)
    ·
      refine ⟨151047258902056281443331953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402792690405483417182218541 151047258902056281443331953)
      ·
        refine ⟨113285444176542211082498965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151047258902056281443331953 113285444176542211082498965)
        ·
          refine ⟨5310255195775416144492139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113285444176542211082498965 5310255195775416144492139)
          ·
            refine ⟨7965382793663124216738209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5310255195775416144492139 7965382793663124216738209)
            ·
              refine ⟨5974037095247343162553657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7965382793663124216738209 5974037095247343162553657)
              ·
                refine ⟨4480527821435507371915243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5974037095247343162553657 4480527821435507371915243)
                ·
                  refine ⟨6720791732153261057872865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480527821435507371915243 6720791732153261057872865)
                  ·
                    refine ⟨5040593799114945793404649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6720791732153261057872865 5040593799114945793404649)
                    ·
                      refine ⟨3780445349336209345053487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5040593799114945793404649 3780445349336209345053487)
                      ·
                        rfl

theorem cell23_7362391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_7362391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362391 prefixEnd_7362391 := by exact prefixLift 7362391
  have htrace : WordTrace (prefixWord ++ tailWord_7362391) baseStart_7362391 baseEnd_7362391 := by
    simpa [prefixWord, tailWord_7362391, baseEnd_7362391] using wordTrace_append hprefix tailTrace_7362391
  have hstable : (prefixWord ++ tailWord_7362391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362391).length < 2 ^ (prefixWord ++ tailWord_7362391).sum := by decide
  have hdescent : baseEnd_7362391 < baseStart_7362391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362413 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_7362413 : Nat := 118140960795 + 7362413 * 2 ^ 59
def prefixEnd_7362413 : Nat := 4983230072969 + 3 ^ 40 * 7362413 * 2
def baseEnd_7362413 : Nat := 3780456645910608258978385

theorem tailTrace_7362413 : CollatzResearch.WordTrace tailWord_7362413 prefixEnd_7362413 3780456645910608258978385 := by
  unfold tailWord_7362413
  simp only [CollatzResearch.WordTrace]
  refine ⟨268529262676242575878779893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179019508450828383919186595 268529262676242575878779893)
  ·
    refine ⟨25174618375897741488635615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268529262676242575878779893 25174618375897741488635615)
    ·
      refine ⟨37761927563846612232953423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25174618375897741488635615 37761927563846612232953423)
      ·
        refine ⟨56642891345769918349430135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37761927563846612232953423 56642891345769918349430135)
        ·
          refine ⟨84964337018654877524145203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56642891345769918349430135 84964337018654877524145203)
          ·
            refine ⟨127446505527982316286217805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84964337018654877524145203 127446505527982316286217805)
            ·
              refine ⟨47792439572993368607331677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127446505527982316286217805 47792439572993368607331677)
              ·
                refine ⟨17922164839872513227749379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47792439572993368607331677 17922164839872513227749379)
                ·
                  refine ⟨26883247259808769841624069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17922164839872513227749379 26883247259808769841624069)
                  ·
                    refine ⟨5040608861214144345304513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26883247259808769841624069 5040608861214144345304513)
                    ·
                      refine ⟨3780456645910608258978385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5040608861214144345304513 3780456645910608258978385)
                      ·
                        rfl

theorem cell23_7362413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_7362413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362413 prefixEnd_7362413 := by exact prefixLift 7362413
  have htrace : WordTrace (prefixWord ++ tailWord_7362413) baseStart_7362413 baseEnd_7362413 := by
    simpa [prefixWord, tailWord_7362413, baseEnd_7362413] using wordTrace_append hprefix tailTrace_7362413
  have hstable : (prefixWord ++ tailWord_7362413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362413).length < 2 ^ (prefixWord ++ tailWord_7362413).sum := by decide
  have hdescent : baseEnd_7362413 < baseStart_7362413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362429 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_7362429 : Nat := 118140960795 + 7362429 * 2 ^ 59
def prefixEnd_7362429 : Nat := 4983230072969 + 3 ^ 40 * 7362429 * 2
def baseEnd_7362429 : Nat := 3780464861601080196378311

theorem tailTrace_7362429 : CollatzResearch.WordTrace tailWord_7362429 prefixEnd_7362429 3780464861601080196378311 := by
  unfold tailWord_7362429
  simp only [CollatzResearch.WordTrace]
  refine ⟨268529846244184610611362341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179019897496123073740908227 268529846244184610611362341)
  ·
    refine ⟨50349346170784614489630439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268529846244184610611362341 50349346170784614489630439)
    ·
      refine ⟨75524019256176921734445659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50349346170784614489630439 75524019256176921734445659)
      ·
        refine ⟨113286028884265382601668489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75524019256176921734445659 113286028884265382601668489)
        ·
          refine ⟨84964521663199036951251367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113286028884265382601668489 84964521663199036951251367)
          ·
            refine ⟨127446782494798555426877051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84964521663199036951251367 127446782494798555426877051)
            ·
              refine ⟨191170173742197833140315577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127446782494798555426877051 191170173742197833140315577)
              ·
                refine ⟨143377630306648374855236683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191170173742197833140315577 143377630306648374855236683)
                ·
                  refine ⟨215066445459972562282855025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143377630306648374855236683 215066445459972562282855025)
                  ·
                    refine ⟨161299834094979421712141269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 215066445459972562282855025 161299834094979421712141269)
                    ·
                      refine ⟨3780464861601080196378311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161299834094979421712141269 3780464861601080196378311)
                      ·
                        rfl

theorem cell23_7362429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_7362429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362429 prefixEnd_7362429 := by exact prefixLift 7362429
  have htrace : WordTrace (prefixWord ++ tailWord_7362429) baseStart_7362429 baseEnd_7362429 := by
    simpa [prefixWord, tailWord_7362429, baseEnd_7362429] using wordTrace_append hprefix tailTrace_7362429
  have hstable : (prefixWord ++ tailWord_7362429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362429).length < 2 ^ (prefixWord ++ tailWord_7362429).sum := by decide
  have hdescent : baseEnd_7362429 < baseStart_7362429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362479 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 2, 8]
def baseStart_7362479 : Nat := 118140960795 + 7362479 * 2 ^ 59
def prefixEnd_7362479 : Nat := 4983230072969 + 3 ^ 40 * 7362479 * 2
def baseEnd_7362479 : Nat := 1260163511877935000251027

theorem tailTrace_7362479 : CollatzResearch.WordTrace tailWord_7362479 prefixEnd_7362479 1260163511877935000251027 := by
  unfold tailWord_7362479
  simp only [CollatzResearch.WordTrace]
  refine ⟨268531669894003469150682491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179021113262668979433788327 268531669894003469150682491)
  ·
    refine ⟨402797504841005203726023737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268531669894003469150682491 402797504841005203726023737)
    ·
      refine ⟨302098128630753902794517803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402797504841005203726023737 302098128630753902794517803)
      ·
        refine ⟨453147192946130854191776705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302098128630753902794517803 453147192946130854191776705)
        ·
          refine ⟨339860394709598140643832529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453147192946130854191776705 339860394709598140643832529)
          ·
            refine ⟨254895296032198605482874397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339860394709598140643832529 254895296032198605482874397)
            ·
              refine ⟨95585736012074477056077899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254895296032198605482874397 95585736012074477056077899)
              ·
                refine ⟨143378604018111715584116849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95585736012074477056077899 143378604018111715584116849)
                ·
                  refine ⟨107533953013583786688087637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143378604018111715584116849 107533953013583786688087637)
                  ·
                    refine ⟨1260163511877935000251027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107533953013583786688087637 1260163511877935000251027)
                    ·
                      rfl

theorem cell23_7362479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_7362479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362479 prefixEnd_7362479 := by exact prefixLift 7362479
  have htrace : WordTrace (prefixWord ++ tailWord_7362479) baseStart_7362479 baseEnd_7362479 := by
    simpa [prefixWord, tailWord_7362479, baseEnd_7362479] using wordTrace_append hprefix tailTrace_7362479
  have hstable : (prefixWord ++ tailWord_7362479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362479).length < 2 ^ (prefixWord ++ tailWord_7362479).sum := by decide
  have hdescent : baseEnd_7362479 < baseStart_7362479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362564 : List Nat := [2, 3, 2, 4, 1, 1, 1, 4, 1, 4]
def baseStart_7362564 : Nat := 118140960795 + 7362564 * 2 ^ 59
def prefixEnd_7362564 : Nat := 4983230072969 + 3 ^ 40 * 7362564 * 2
def baseEnd_7362564 : Nat := 1260178060496479056063397

theorem tailTrace_7362564 : CollatzResearch.WordTrace tailWord_7362564 prefixEnd_7362564 1260178060496479056063397 := by
  unfold tailWord_7362564
  simp only [CollatzResearch.WordTrace]
  refine ⟨134267385049347764333763373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179023180065797019111684497 134267385049347764333763373)
  ·
    refine ⟨50350269393505411625161265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134267385049347764333763373 50350269393505411625161265)
    ·
      refine ⟨37762702045129058718870949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50350269393505411625161265 37762702045129058718870949)
      ·
        refine ⟨7080506633461698509788303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37762702045129058718870949 7080506633461698509788303)
        ·
          refine ⟨10620759950192547764682455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7080506633461698509788303 10620759950192547764682455)
          ·
            refine ⟨15931139925288821647023683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10620759950192547764682455 15931139925288821647023683)
            ·
              refine ⟨23896709887933232470535525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15931139925288821647023683 23896709887933232470535525)
              ·
                refine ⟨4480633103987481088225411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23896709887933232470535525 4480633103987481088225411)
                ·
                  refine ⟨6720949655981221632338117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480633103987481088225411 6720949655981221632338117)
                  ·
                    refine ⟨1260178060496479056063397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6720949655981221632338117 1260178060496479056063397)
                    ·
                      rfl

theorem cell23_7362564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_7362564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362564 prefixEnd_7362564 := by exact prefixLift 7362564
  have htrace : WordTrace (prefixWord ++ tailWord_7362564) baseStart_7362564 baseEnd_7362564 := by
    simpa [prefixWord, tailWord_7362564, baseEnd_7362564] using wordTrace_append hprefix tailTrace_7362564
  have hstable : (prefixWord ++ tailWord_7362564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362564).length < 2 ^ (prefixWord ++ tailWord_7362564).sum := by decide
  have hdescent : baseEnd_7362564 < baseStart_7362564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362597 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 2, 3, 2]
def baseStart_7362597 : Nat := 118140960795 + 7362597 * 2 ^ 59
def prefixEnd_7362597 : Nat := 4983230072969 + 3 ^ 40 * 7362597 * 2
def baseEnd_7362597 : Nat := 3780551126351035539077539

theorem tailTrace_7362597 : CollatzResearch.WordTrace tailWord_7362597 prefixEnd_7362597 3780551126351035539077539 := by
  unfold tailWord_7362597
  simp only [CollatzResearch.WordTrace]
  refine ⟨268535973707575975303478045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179023982471717316868985363 268535973707575975303478045)
  ·
    refine ⟨100700990140340990738804267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268535973707575975303478045 100700990140340990738804267)
    ·
      refine ⟨151051485210511486108206401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100700990140340990738804267 151051485210511486108206401)
      ·
        refine ⟨113288613907883614581154801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151051485210511486108206401 113288613907883614581154801)
        ·
          refine ⟨84966460430912710935866101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113288613907883614581154801 84966460430912710935866101)
          ·
            refine ⟨7965605665398066650237447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84966460430912710935866101 7965605665398066650237447)
            ·
              refine ⟨11948408498097099975356171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7965605665398066650237447 11948408498097099975356171)
              ·
                refine ⟨17922612747145649963034257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11948408498097099975356171 17922612747145649963034257)
                ·
                  refine ⟨13441959560359237472275693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17922612747145649963034257 13441959560359237472275693)
                  ·
                    refine ⟨5040734835134714052103385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13441959560359237472275693 5040734835134714052103385)
                    ·
                      refine ⟨3780551126351035539077539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5040734835134714052103385 3780551126351035539077539)
                      ·
                        rfl

theorem cell23_7362597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_7362597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362597 prefixEnd_7362597 := by exact prefixLift 7362597
  have htrace : WordTrace (prefixWord ++ tailWord_7362597) baseStart_7362597 baseEnd_7362597 := by
    simpa [prefixWord, tailWord_7362597, baseEnd_7362597] using wordTrace_append hprefix tailTrace_7362597
  have hstable : (prefixWord ++ tailWord_7362597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362597).length < 2 ^ (prefixWord ++ tailWord_7362597).sum := by decide
  have hdescent : baseEnd_7362597 < baseStart_7362597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362610 : List Nat := [3, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4]
def baseStart_7362610 : Nat := 118140960795 + 7362610 * 2 ^ 59
def prefixEnd_7362610 : Nat := 4983230072969 + 3 ^ 40 * 7362610 * 2
def baseEnd_7362610 : Nat := 3780557801599543988214979

theorem tailTrace_7362610 : CollatzResearch.WordTrace tailWord_7362610 prefixEnd_7362610 3780557801599543988214979 := by
  unfold tailWord_7362610
  simp only [CollatzResearch.WordTrace]
  refine ⟨67134111964132219630925321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179024298571019252349134189 67134111964132219630925321)
  ·
    refine ⟨50350583973099164723193991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67134111964132219630925321 50350583973099164723193991)
    ·
      refine ⟨75525875959648747084790987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50350583973099164723193991 75525875959648747084790987)
      ·
        refine ⟨113288813939473120627186481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75525875959648747084790987 113288813939473120627186481)
        ·
          refine ⟨84966610454604840470389861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113288813939473120627186481 84966610454604840470389861)
          ·
            refine ⟨15931239460238407588198099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84966610454604840470389861 15931239460238407588198099)
            ·
              refine ⟨23896859190357611382297149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15931239460238407588198099 23896859190357611382297149)
              ·
                refine ⟨8961322196384104268361431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23896859190357611382297149 8961322196384104268361431)
                ·
                  refine ⟨13441983294576156402542147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8961322196384104268361431 13441983294576156402542147)
                  ·
                    refine ⟨20162974941864234603813221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13441983294576156402542147 20162974941864234603813221)
                    ·
                      refine ⟨3780557801599543988214979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20162974941864234603813221 3780557801599543988214979)
                      ·
                        rfl

theorem cell23_7362610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_7362610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362610 prefixEnd_7362610 := by exact prefixLift 7362610
  have htrace : WordTrace (prefixWord ++ tailWord_7362610) baseStart_7362610 baseEnd_7362610 := by
    simpa [prefixWord, tailWord_7362610, baseEnd_7362610] using wordTrace_append hprefix tailTrace_7362610
  have hstable : (prefixWord ++ tailWord_7362610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362610).length < 2 ^ (prefixWord ++ tailWord_7362610).sum := by decide
  have hdescent : baseEnd_7362610 < baseStart_7362610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362660 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 4, 1, 3]
def baseStart_7362660 : Nat := 118140960795 + 7362660 * 2 ^ 59
def prefixEnd_7362660 : Nat := 4983230072969 + 3 ^ 40 * 7362660 * 2
def baseEnd_7362660 : Nat := 3780583475632268792589749

theorem tailTrace_7362660 : CollatzResearch.WordTrace tailWord_7362660 prefixEnd_7362660 3780583475632268792589749 := by
  unfold tailWord_7362660
  simp only [CollatzResearch.WordTrace]
  refine ⟨134269135753173868531510717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179025514337565158042014289 134269135753173868531510717)
  ·
    refine ⟨50350925907440200699316519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134269135753173868531510717 50350925907440200699316519)
    ·
      refine ⟨75526388861160301048974779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50350925907440200699316519 75526388861160301048974779)
      ·
        refine ⟨113289583291740451573462169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75526388861160301048974779 113289583291740451573462169)
        ·
          refine ⟨84967187468805338680096627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113289583291740451573462169 84967187468805338680096627)
          ·
            refine ⟨127450781203208008020144941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84967187468805338680096627 127450781203208008020144941)
            ·
              refine ⟨47794042951203003007554353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127450781203208008020144941 47794042951203003007554353)
              ·
                refine ⟨35845532213402252255665765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47794042951203003007554353 35845532213402252255665765)
                ·
                  refine ⟨6721037290012922297937331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35845532213402252255665765 6721037290012922297937331)
                  ·
                    refine ⟨10081555935019383446905997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6721037290012922297937331 10081555935019383446905997)
                    ·
                      refine ⟨3780583475632268792589749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10081555935019383446905997 3780583475632268792589749)
                      ·
                        rfl

theorem cell23_7362660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_7362660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362660 prefixEnd_7362660 := by exact prefixLift 7362660
  have htrace : WordTrace (prefixWord ++ tailWord_7362660) baseStart_7362660 baseEnd_7362660 := by
    simpa [prefixWord, tailWord_7362660, baseEnd_7362660] using wordTrace_append hprefix tailTrace_7362660
  have hstable : (prefixWord ++ tailWord_7362660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362660).length < 2 ^ (prefixWord ++ tailWord_7362660).sum := by decide
  have hdescent : baseEnd_7362660 < baseStart_7362660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362661 : List Nat := [1, 3, 1, 3, 2, 4, 1, 3, 1, 2, 2]
def baseStart_7362661 : Nat := 118140960795 + 7362661 * 2 ^ 59
def prefixEnd_7362661 : Nat := 4983230072969 + 3 ^ 40 * 7362661 * 2
def baseEnd_7362661 : Nat := 3780583989112923288677245

theorem tailTrace_7362661 : CollatzResearch.WordTrace tailWord_7362661 prefixEnd_7362661 3780583989112923288677245 := by
  unfold tailWord_7362661
  simp only [CollatzResearch.WordTrace]
  refine ⟨268538307979344114233807837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179025538652896076155871891 268538307979344114233807837)
  ·
    refine ⟨100701865492254042837677939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268538307979344114233807837 100701865492254042837677939)
    ·
      refine ⟨151052798238381064256516909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100701865492254042837677939 151052798238381064256516909)
      ·
        refine ⟨56644799339392899096193841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151052798238381064256516909 56644799339392899096193841)
        ·
          refine ⟨42483599504544674322145381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56644799339392899096193841 42483599504544674322145381)
          ·
            refine ⟨7965674907102126435402259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42483599504544674322145381 7965674907102126435402259)
            ·
              refine ⟨11948512360653189653103389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7965674907102126435402259 11948512360653189653103389)
              ·
                refine ⟨4480692135244946119913771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11948512360653189653103389 4480692135244946119913771)
                ·
                  refine ⟨6721038202867419179870657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480692135244946119913771 6721038202867419179870657)
                  ·
                    refine ⟨5040778652150564384902993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6721038202867419179870657 5040778652150564384902993)
                    ·
                      refine ⟨3780583989112923288677245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5040778652150564384902993 3780583989112923288677245)
                      ·
                        rfl

theorem cell23_7362661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_7362661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362661 prefixEnd_7362661 := by exact prefixLift 7362661
  have htrace : WordTrace (prefixWord ++ tailWord_7362661) baseStart_7362661 baseEnd_7362661 := by
    simpa [prefixWord, tailWord_7362661, baseEnd_7362661] using wordTrace_append hprefix tailTrace_7362661
  have hstable : (prefixWord ++ tailWord_7362661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362661).length < 2 ^ (prefixWord ++ tailWord_7362661).sum := by decide
  have hdescent : baseEnd_7362661 < baseStart_7362661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362678 : List Nat := [5, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2]
def baseStart_7362678 : Nat := 118140960795 + 7362678 * 2 ^ 59
def prefixEnd_7362678 : Nat := 4983230072969 + 3 ^ 40 * 7362678 * 2
def baseEnd_7362678 : Nat := 3780592718284049722164667

theorem tailTrace_7362678 : CollatzResearch.WordTrace tailWord_7362678 prefixEnd_7362678 3780592718284049722164667 := by
  unfold tailWord_7362678
  simp only [CollatzResearch.WordTrace]
  refine ⟨16783683001267657883573543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179025952013521684091451125 16783683001267657883573543)
  ·
    refine ⟨25175524501901486825360315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16783683001267657883573543 25175524501901486825360315)
    ·
      refine ⟨37763286752852230238040473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25175524501901486825360315 37763286752852230238040473)
      ·
        refine ⟨28322465064639172678530355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37763286752852230238040473 28322465064639172678530355)
        ·
          refine ⟨42483697596958759017795533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28322465064639172678530355 42483697596958759017795533)
          ·
            refine ⟨15931386598859534631673325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42483697596958759017795533 15931386598859534631673325)
            ·
              refine ⟨5974269974572325486877497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15931386598859534631673325 5974269974572325486877497)
              ·
                refine ⟨4480702480929244115158123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5974269974572325486877497 4480702480929244115158123)
                ·
                  refine ⟨6721053721393866172737185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480702480929244115158123 6721053721393866172737185)
                  ·
                    refine ⟨5040790291045399629552889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6721053721393866172737185 5040790291045399629552889)
                    ·
                      refine ⟨3780592718284049722164667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5040790291045399629552889 3780592718284049722164667)
                      ·
                        rfl

theorem cell23_7362678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_7362678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362678 prefixEnd_7362678 := by exact prefixLift 7362678
  have htrace : WordTrace (prefixWord ++ tailWord_7362678) baseStart_7362678 baseEnd_7362678 := by
    simpa [prefixWord, tailWord_7362678, baseEnd_7362678] using wordTrace_append hprefix tailTrace_7362678
  have hstable : (prefixWord ++ tailWord_7362678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362678).length < 2 ^ (prefixWord ++ tailWord_7362678).sum := by decide
  have hdescent : baseEnd_7362678 < baseStart_7362678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362717 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_7362717 : Nat := 118140960795 + 7362717 * 2 ^ 59
def prefixEnd_7362717 : Nat := 4983230072969 + 3 ^ 40 * 7362717 * 2
def baseEnd_7362717 : Nat := 3780612744029575069576987

theorem tailTrace_7362717 : CollatzResearch.WordTrace tailWord_7362717 prefixEnd_7362717 3780612744029575069576987 := by
  unfold tailWord_7362717
  simp only [CollatzResearch.WordTrace]
  refine ⟨268540350467141235797846405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179026900311427490531897603 268540350467141235797846405)
  ·
    refine ⟨50351315712588981712096201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268540350467141235797846405 50351315712588981712096201)
    ·
      refine ⟨37763486784441736284072151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50351315712588981712096201 37763486784441736284072151)
      ·
        refine ⟨56645230176662604426108227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37763486784441736284072151 56645230176662604426108227)
        ·
          refine ⟨84967845264993906639162341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56645230176662604426108227 84967845264993906639162341)
          ·
            refine ⟨15931470987186357494842939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84967845264993906639162341 15931470987186357494842939)
            ·
              refine ⟨23897206480779536242264409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15931470987186357494842939 23897206480779536242264409)
              ·
                refine ⟨17922904860584652181698307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23897206480779536242264409 17922904860584652181698307)
                ·
                  refine ⟨26884357290876978272547461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17922904860584652181698307 26884357290876978272547461)
                  ·
                    refine ⟨5040816992039433426102649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26884357290876978272547461 5040816992039433426102649)
                    ·
                      refine ⟨3780612744029575069576987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5040816992039433426102649 3780612744029575069576987)
                      ·
                        rfl

theorem cell23_7362717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_7362717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362717 prefixEnd_7362717 := by exact prefixLift 7362717
  have htrace : WordTrace (prefixWord ++ tailWord_7362717) baseStart_7362717 baseEnd_7362717 := by
    simpa [prefixWord, tailWord_7362717, baseEnd_7362717] using wordTrace_append hprefix tailTrace_7362717
  have hstable : (prefixWord ++ tailWord_7362717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362717).length < 2 ^ (prefixWord ++ tailWord_7362717).sum := by decide
  have hdescent : baseEnd_7362717 < baseStart_7362717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362760 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 4, 5, 2]
def baseStart_7362760 : Nat := 118140960795 + 7362760 * 2 ^ 59
def prefixEnd_7362760 : Nat := 4983230072969 + 3 ^ 40 * 7362760 * 2
def baseEnd_7362760 : Nat := 3780634823697718401339289

theorem tailTrace_7362760 : CollatzResearch.WordTrace tailWord_7362760 prefixEnd_7362760 3780634823697718401339289 := by
  unfold tailWord_7362760
  simp only [CollatzResearch.WordTrace]
  refine ⟨134270959402992727070830867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179027945870656969427774489 134270959402992727070830867)
  ·
    refine ⟨201406439104489090606246301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134270959402992727070830867 201406439104489090606246301)
    ·
      refine ⟨75527414664183408977342363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201406439104489090606246301 75527414664183408977342363)
      ·
        refine ⟨113291121996275113466013545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75527414664183408977342363 113291121996275113466013545)
        ·
          refine ⟨84968341497206335099510159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113291121996275113466013545 84968341497206335099510159)
          ·
            refine ⟨127452512245809502649265239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84968341497206335099510159 127452512245809502649265239)
            ·
              refine ⟨191178768368714253973897859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127452512245809502649265239 191178768368714253973897859)
              ·
                refine ⟨286768152553071380960846789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191178768368714253973897859 286768152553071380960846789)
                ·
                  refine ⟨53769028603700883930158773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286768152553071380960846789 53769028603700883930158773)
                  ·
                    refine ⟨5040846431596957868452385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53769028603700883930158773 5040846431596957868452385)
                    ·
                      refine ⟨3780634823697718401339289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5040846431596957868452385 3780634823697718401339289)
                      ·
                        rfl

theorem cell23_7362760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_7362760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362760 prefixEnd_7362760 := by exact prefixLift 7362760
  have htrace : WordTrace (prefixWord ++ tailWord_7362760) baseStart_7362760 baseEnd_7362760 := by
    simpa [prefixWord, tailWord_7362760, baseEnd_7362760] using wordTrace_append hprefix tailTrace_7362760
  have hstable : (prefixWord ++ tailWord_7362760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362760).length < 2 ^ (prefixWord ++ tailWord_7362760).sum := by decide
  have hdescent : baseEnd_7362760 < baseStart_7362760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362770 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_7362770 : Nat := 118140960795 + 7362770 * 2 ^ 59
def prefixEnd_7362770 : Nat := 4983230072969 + 3 ^ 40 * 7362770 * 2
def baseEnd_7362770 : Nat := 1260213319501421120738081

theorem tailTrace_7362770 : CollatzResearch.WordTrace tailWord_7362770 prefixEnd_7362770 1260213319501421120738081 := by
  unfold tailWord_7362770
  simp only [CollatzResearch.WordTrace]
  refine ⟨67135570883987306462381441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179028189023966150566350509 67135570883987306462381441)
  ·
    refine ⟨50351678162990479846786081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67135570883987306462381441 50351678162990479846786081)
    ·
      refine ⟨37763758622242859885089561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50351678162990479846786081 37763758622242859885089561)
      ·
        refine ⟨28322818966682144913817171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37763758622242859885089561 28322818966682144913817171)
        ·
          refine ⟨42484228450023217370725757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28322818966682144913817171 42484228450023217370725757)
          ·
            refine ⟨15931585668758706514022159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42484228450023217370725757 15931585668758706514022159)
            ·
              refine ⟨23897378503138059771033239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15931585668758706514022159 23897378503138059771033239)
              ·
                refine ⟨35846067754707089656549859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23897378503138059771033239 35846067754707089656549859)
                ·
                  refine ⟨53769101632060634484824789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35846067754707089656549859 53769101632060634484824789)
                  ·
                    refine ⟨1260213319501421120738081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53769101632060634484824789 1260213319501421120738081)
                    ·
                      rfl

theorem cell23_7362770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_7362770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362770 prefixEnd_7362770 := by exact prefixLift 7362770
  have htrace : WordTrace (prefixWord ++ tailWord_7362770) baseStart_7362770 baseEnd_7362770 := by
    simpa [prefixWord, tailWord_7362770, baseEnd_7362770] using wordTrace_append hprefix tailTrace_7362770
  have hstable : (prefixWord ++ tailWord_7362770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362770).length < 2 ^ (prefixWord ++ tailWord_7362770).sum := by decide
  have hdescent : baseEnd_7362770 < baseStart_7362770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362774 : List Nat := [5, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_7362774 : Nat := 118140960795 + 7362774 * 2 ^ 59
def prefixEnd_7362774 : Nat := 4983230072969 + 3 ^ 40 * 7362774 * 2
def baseEnd_7362774 : Nat := 420071334714097927396025

theorem tailTrace_7362774 : CollatzResearch.WordTrace tailWord_7362774 prefixEnd_7362774 420071334714097927396025 := by
  unfold tailWord_7362774
  simp only [CollatzResearch.WordTrace]
  refine ⟨16783901839245920908291961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179028286285289823021780917 16783901839245920908291961)
  ·
    refine ⟨12587926379434440681218971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16783901839245920908291961 12587926379434440681218971)
    ·
      refine ⟨18881889569151661021828457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12587926379434440681218971 18881889569151661021828457)
      ·
        refine ⟨14161417176863745766371343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18881889569151661021828457 14161417176863745766371343)
        ·
          refine ⟨21242125765295618649557015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14161417176863745766371343 21242125765295618649557015)
          ·
            refine ⟨31863188647943427974335523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21242125765295618649557015 31863188647943427974335523)
            ·
              refine ⟨47794782971915141961503285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31863188647943427974335523 47794782971915141961503285)
              ·
                refine ⟨4480760903617044558890933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47794782971915141961503285 4480760903617044558890933)
                ·
                  refine ⟨420071334714097927396025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4480760903617044558890933 420071334714097927396025)
                  ·
                    rfl

theorem cell23_7362774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_7362774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362774 prefixEnd_7362774 := by exact prefixLift 7362774
  have htrace : WordTrace (prefixWord ++ tailWord_7362774) baseStart_7362774 baseEnd_7362774 := by
    simpa [prefixWord, tailWord_7362774, baseEnd_7362774] using wordTrace_append hprefix tailTrace_7362774
  have hstable : (prefixWord ++ tailWord_7362774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362774).length < 2 ^ (prefixWord ++ tailWord_7362774).sum := by decide
  have hdescent : baseEnd_7362774 < baseStart_7362774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362803 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 6]
def baseStart_7362803 : Nat := 118140960795 + 7362803 * 2 ^ 59
def prefixEnd_7362803 : Nat := 4983230072969 + 3 ^ 40 * 7362803 * 2
def baseEnd_7362803 : Nat := 3780656903365861733101591

theorem tailTrace_7362803 : CollatzResearch.WordTrace tailWord_7362803 prefixEnd_7362803 3780656903365861733101591 := by
  unfold tailWord_7362803
  simp only [CollatzResearch.WordTrace]
  refine ⟨268543487144829672485477063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179028991429886448323651375 268543487144829672485477063)
  ·
    refine ⟨402815230717244508728215595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268543487144829672485477063 402815230717244508728215595)
    ·
      refine ⟨604222846075866763092323393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402815230717244508728215595 604222846075866763092323393)
      ·
        refine ⟨453167134556900072319242545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604222846075866763092323393 453167134556900072319242545)
        ·
          refine ⟨339875350917675054239431909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453167134556900072319242545 339875350917675054239431909)
          ·
            refine ⟨63726628297064072669893483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339875350917675054239431909 63726628297064072669893483)
            ·
              refine ⟨95589942445596109004840225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63726628297064072669893483 95589942445596109004840225)
              ·
                refine ⟨71692456834197081753630169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95589942445596109004840225 71692456834197081753630169)
                ·
                  refine ⟨53769342625647811315222627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71692456834197081753630169 53769342625647811315222627)
                  ·
                    refine ⟨80654013938471716972833941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53769342625647811315222627 80654013938471716972833941)
                    ·
                      refine ⟨3780656903365861733101591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80654013938471716972833941 3780656903365861733101591)
                      ·
                        rfl

theorem cell23_7362803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_7362803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362803 prefixEnd_7362803 := by exact prefixLift 7362803
  have htrace : WordTrace (prefixWord ++ tailWord_7362803) baseStart_7362803 baseEnd_7362803 := by
    simpa [prefixWord, tailWord_7362803, baseEnd_7362803] using wordTrace_append hprefix tailTrace_7362803
  have hstable : (prefixWord ++ tailWord_7362803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362803).length < 2 ^ (prefixWord ++ tailWord_7362803).sum := by decide
  have hdescent : baseEnd_7362803 < baseStart_7362803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362810 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3]
def baseStart_7362810 : Nat := 118140960795 + 7362810 * 2 ^ 59
def prefixEnd_7362810 : Nat := 4983230072969 + 3 ^ 40 * 7362810 * 2
def baseEnd_7362810 : Nat := 3780660497730443205714059

theorem tailTrace_7362810 : CollatzResearch.WordTrace tailWord_7362810 prefixEnd_7362810 3780660497730443205714059 := by
  unfold tailWord_7362810
  simp only [CollatzResearch.WordTrace]
  refine ⟨67135935613951078170245471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179029161637202875120654589 67135935613951078170245471)
  ·
    refine ⟨100703903420926617255368207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67135935613951078170245471 100703903420926617255368207)
    ·
      refine ⟨151055855131389925883052311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100703903420926617255368207 151055855131389925883052311)
      ·
        refine ⟨226583782697084888824578467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151055855131389925883052311 226583782697084888824578467)
        ·
          refine ⟨339875674045627333236867701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226583782697084888824578467 339875674045627333236867701)
          ·
            refine ⟨31863344441777562490956347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 339875674045627333236867701 31863344441777562490956347)
            ·
              refine ⟨47795016662666343736434521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31863344441777562490956347 47795016662666343736434521)
              ·
                refine ⟨35846262496999757802325891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47795016662666343736434521 35846262496999757802325891)
                ·
                  refine ⟨53769393745499636703488837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35846262496999757802325891 53769393745499636703488837)
                  ·
                    refine ⟨10081761327281181881904157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53769393745499636703488837 10081761327281181881904157)
                    ·
                      refine ⟨3780660497730443205714059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10081761327281181881904157 3780660497730443205714059)
                      ·
                        rfl

theorem cell23_7362810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_7362810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362810 prefixEnd_7362810 := by exact prefixLift 7362810
  have htrace : WordTrace (prefixWord ++ tailWord_7362810) baseStart_7362810 baseEnd_7362810 := by
    simpa [prefixWord, tailWord_7362810, baseEnd_7362810] using wordTrace_append hprefix tailTrace_7362810
  have hstable : (prefixWord ++ tailWord_7362810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362810).length < 2 ^ (prefixWord ++ tailWord_7362810).sum := by decide
  have hdescent : baseEnd_7362810 < baseStart_7362810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362867 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 4, 3, 2]
def baseStart_7362867 : Nat := 118140960795 + 7362867 * 2 ^ 59
def prefixEnd_7362867 : Nat := 4983230072969 + 3 ^ 40 * 7362867 * 2
def baseEnd_7362867 : Nat := 3780689766127749482701297

theorem tailTrace_7362867 : CollatzResearch.WordTrace tailWord_7362867 prefixEnd_7362867 3780689766127749482701297 := by
  unfold tailWord_7362867
  simp only [CollatzResearch.WordTrace]
  refine ⟨268545821416597811415806855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179030547611065207610537903 268545821416597811415806855)
  ·
    refine ⟨402818732124896717123710283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268545821416597811415806855 402818732124896717123710283)
    ·
      refine ⟨604228098187345075685565425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402818732124896717123710283 604228098187345075685565425)
      ·
        refine ⟨453171073640508806764174069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604228098187345075685565425 453171073640508806764174069)
        ·
          refine ⟨42484788153797700634141319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 453171073640508806764174069 42484788153797700634141319)
          ·
            refine ⟨63727182230696550951211979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42484788153797700634141319 63727182230696550951211979)
            ·
              refine ⟨95590773346044826426817969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63727182230696550951211979 95590773346044826426817969)
              ·
                refine ⟨71693080009533619820113477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95590773346044826426817969 71693080009533619820113477)
                ·
                  refine ⟨13442452501787553716271277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71693080009533619820113477 13442452501787553716271277)
                  ·
                    refine ⟨5040919688170332643601729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13442452501787553716271277 5040919688170332643601729)
                    ·
                      refine ⟨3780689766127749482701297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5040919688170332643601729 3780689766127749482701297)
                      ·
                        rfl

theorem cell23_7362867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 3, 2].length) (baseStart_7362867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362867 prefixEnd_7362867 := by exact prefixLift 7362867
  have htrace : WordTrace (prefixWord ++ tailWord_7362867) baseStart_7362867 baseEnd_7362867 := by
    simpa [prefixWord, tailWord_7362867, baseEnd_7362867] using wordTrace_append hprefix tailTrace_7362867
  have hstable : (prefixWord ++ tailWord_7362867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362867).length < 2 ^ (prefixWord ++ tailWord_7362867).sum := by decide
  have hdescent : baseEnd_7362867 < baseStart_7362867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362917 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 3, 2, 3]
def baseStart_7362917 : Nat := 118140960795 + 7362917 * 2 ^ 59
def prefixEnd_7362917 : Nat := 4983230072969 + 3 ^ 40 * 7362917 * 2
def baseEnd_7362917 : Nat := 3780715440160474287076067

theorem tailTrace_7362917 : CollatzResearch.WordTrace tailWord_7362917 prefixEnd_7362917 3780715440160474287076067 := by
  unfold tailWord_7362917
  simp only [CollatzResearch.WordTrace]
  refine ⟨268547645066416669955127005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179031763377611113303418003 268547645066416669955127005)
  ·
    refine ⟨100705366899906251233172627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268547645066416669955127005 100705366899906251233172627)
    ·
      refine ⟨151058050349859376849758941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100705366899906251233172627 151058050349859376849758941)
      ·
        refine ⟨56646768881197266318659603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151058050349859376849758941 56646768881197266318659603)
        ·
          refine ⟨84970153321795899477989405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56646768881197266318659603 84970153321795899477989405)
          ·
            refine ⟨31863807495673462304246027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84970153321795899477989405 31863807495673462304246027)
            ·
              refine ⟨47795711243510193456369041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31863807495673462304246027 47795711243510193456369041)
              ·
                refine ⟨35846783432632645092276781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47795711243510193456369041 35846783432632645092276781)
                ·
                  refine ⟨13442543787237241909603793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35846783432632645092276781 13442543787237241909603793)
                  ·
                    refine ⟨10081907840427931432202845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13442543787237241909603793 10081907840427931432202845)
                    ·
                      refine ⟨3780715440160474287076067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10081907840427931432202845 3780715440160474287076067)
                      ·
                        rfl

theorem cell23_7362917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_7362917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362917 prefixEnd_7362917 := by exact prefixLift 7362917
  have htrace : WordTrace (prefixWord ++ tailWord_7362917) baseStart_7362917 baseEnd_7362917 := by
    simpa [prefixWord, tailWord_7362917, baseEnd_7362917] using wordTrace_append hprefix tailTrace_7362917
  have hstable : (prefixWord ++ tailWord_7362917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362917).length < 2 ^ (prefixWord ++ tailWord_7362917).sum := by decide
  have hdescent : baseEnd_7362917 < baseStart_7362917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362948 : List Nat := [2, 3, 2, 1, 1, 2, 4, 3, 1, 2, 2]
def baseStart_7362948 : Nat := 118140960795 + 7362948 * 2 ^ 59
def prefixEnd_7362948 : Nat := 4983230072969 + 3 ^ 40 * 7362948 * 2
def baseEnd_7362948 : Nat := 3780731358060763665788425

theorem tailTrace_7362948 : CollatzResearch.WordTrace tailWord_7362948 prefixEnd_7362948 3780731358060763665788425 := by
  unfold tailWord_7362948
  simp only [CollatzResearch.WordTrace]
  refine ⟨134274387864652181124752749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179032517152869574833003665 134274387864652181124752749)
  ·
    refine ⟨50352895449244567921782281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134274387864652181124752749 50352895449244567921782281)
    ·
      refine ⟨37764671586933425941336711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50352895449244567921782281 37764671586933425941336711)
      ·
        refine ⟨56647007380400138912005067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37764671586933425941336711 56647007380400138912005067)
        ·
          refine ⟨84970511070600208368007601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56647007380400138912005067 84970511070600208368007601)
          ·
            refine ⟨63727883302950156276005701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84970511070600208368007601 63727883302950156276005701)
            ·
              refine ⟨11948978119303154301751069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63727883302950156276005701 11948978119303154301751069)
              ·
                refine ⟨4480866794738682863156651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11948978119303154301751069 4480866794738682863156651)
                ·
                  refine ⟨6721300192108024294734977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480866794738682863156651 6721300192108024294734977)
                  ·
                    refine ⟨5040975144081018221051233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6721300192108024294734977 5040975144081018221051233)
                    ·
                      refine ⟨3780731358060763665788425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5040975144081018221051233 3780731358060763665788425)
                      ·
                        rfl

theorem cell23_7362948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_7362948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362948 prefixEnd_7362948 := by exact prefixLift 7362948
  have htrace : WordTrace (prefixWord ++ tailWord_7362948) baseStart_7362948 baseEnd_7362948 := by
    simpa [prefixWord, tailWord_7362948, baseEnd_7362948] using wordTrace_append hprefix tailTrace_7362948
  have hstable : (prefixWord ++ tailWord_7362948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362948).length < 2 ^ (prefixWord ++ tailWord_7362948).sum := by decide
  have hdescent : baseEnd_7362948 < baseStart_7362948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7362981 : List Nat := [1, 3, 1, 2, 1, 1, 7, 1, 2, 1, 3]
def baseStart_7362981 : Nat := 118140960795 + 7362981 * 2 ^ 59
def prefixEnd_7362981 : Nat := 4983230072969 + 3 ^ 40 * 7362981 * 2
def baseEnd_7362981 : Nat := 3780748302922362036675773

theorem tailTrace_7362981 : CollatzResearch.WordTrace tailWord_7362981 prefixEnd_7362981 3780748302922362036675773 := by
  unfold tailWord_7362981
  simp only [CollatzResearch.WordTrace]
  refine ⟨268549979338184808885456797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179033319558789872590304531 268549979338184808885456797)
  ·
    refine ⟨100706242251819303332046299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268549979338184808885456797 100706242251819303332046299)
    ·
      refine ⟨151059363377728954998069449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100706242251819303332046299 151059363377728954998069449)
      ·
        refine ⟨113294522533296716248552087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151059363377728954998069449 113294522533296716248552087)
        ·
          refine ⟨169941783799945074372828131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113294522533296716248552087 169941783799945074372828131)
          ·
            refine ⟨254912675699917611559242197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169941783799945074372828131 254912675699917611559242197)
            ·
              refine ⟨5974515836716819020919739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 254912675699917611559242197 5974515836716819020919739)
              ·
                refine ⟨8961773755075228531379609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5974515836716819020919739 8961773755075228531379609)
                ·
                  refine ⟨6721330316306421398534707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8961773755075228531379609 6721330316306421398534707)
                  ·
                    refine ⟨10081995474459632097802061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6721330316306421398534707 10081995474459632097802061)
                    ·
                      refine ⟨3780748302922362036675773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10081995474459632097802061 3780748302922362036675773)
                      ·
                        rfl

theorem cell23_7362981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_7362981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7362981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7362981 prefixEnd_7362981 := by exact prefixLift 7362981
  have htrace : WordTrace (prefixWord ++ tailWord_7362981) baseStart_7362981 baseEnd_7362981 := by
    simpa [prefixWord, tailWord_7362981, baseEnd_7362981] using wordTrace_append hprefix tailTrace_7362981
  have hstable : (prefixWord ++ tailWord_7362981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7362981).length < 2 ^ (prefixWord ++ tailWord_7362981).sum := by decide
  have hdescent : baseEnd_7362981 < baseStart_7362981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7362981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363042 : List Nat := [3, 3, 3, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_7363042 : Nat := 118140960795 + 7363042 * 2 ^ 59
def prefixEnd_7363042 : Nat := 4983230072969 + 3 ^ 40 * 7363042 * 2
def baseEnd_7363042 : Nat := 3780779625242286298012993

theorem tailTrace_7363042 : CollatzResearch.WordTrace tailWord_7363042 prefixEnd_7363042 3780779625242286298012993 := by
  unfold tailWord_7363042
  simp only [CollatzResearch.WordTrace]
  refine ⟨67138051047740954075856845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179034802793975877535618253 67138051047740954075856845)
  ·
    refine ⟨25176769142902857778446317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67138051047740954075856845 25176769142902857778446317)
    ·
      refine ⟨9441288428588571666917369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25176769142902857778446317 9441288428588571666917369)
      ·
        refine ⟨7080966321441428750188027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9441288428588571666917369 7080966321441428750188027)
        ·
          refine ⟨10621449482162143125282041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7080966321441428750188027 10621449482162143125282041)
          ·
            refine ⟨7966087111621607343961531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10621449482162143125282041 7966087111621607343961531)
            ·
              refine ⟨11949130667432411015942297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7966087111621607343961531 11949130667432411015942297)
              ·
                refine ⟨8961848000574308261956723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11949130667432411015942297 8961848000574308261956723)
                ·
                  refine ⟨13442772000861462392935085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8961848000574308261956723 13442772000861462392935085)
                  ·
                    refine ⟨5041039500323048397350657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13442772000861462392935085 5041039500323048397350657)
                    ·
                      refine ⟨3780779625242286298012993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5041039500323048397350657 3780779625242286298012993)
                      ·
                        rfl

theorem cell23_7363042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_7363042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363042 prefixEnd_7363042 := by exact prefixLift 7363042
  have htrace : WordTrace (prefixWord ++ tailWord_7363042) baseStart_7363042 baseEnd_7363042 := by
    simpa [prefixWord, tailWord_7363042, baseEnd_7363042] using wordTrace_append hprefix tailTrace_7363042
  have hstable : (prefixWord ++ tailWord_7363042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363042).length < 2 ^ (prefixWord ++ tailWord_7363042).sum := by decide
  have hdescent : baseEnd_7363042 < baseStart_7363042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363097 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 3, 4, 3]
def baseStart_7363097 : Nat := 118140960795 + 7363097 * 2 ^ 59
def prefixEnd_7363097 : Nat := 4983230072969 + 3 ^ 40 * 7363097 * 2
def baseEnd_7363097 : Nat := 3780807866678283582825239

theorem tailTrace_7363097 : CollatzResearch.WordTrace tailWord_7363097 prefixEnd_7363097 3780807866678283582825239 := by
  unfold tailWord_7363097
  simp only [CollatzResearch.WordTrace]
  refine ⟨268554210205764560696679545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179036140137176373797786363 268554210205764560696679545)
  ·
    refine ⟨201415657654323420522509659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268554210205764560696679545 201415657654323420522509659)
    ·
      refine ⟨302123486481485130783764489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201415657654323420522509659 302123486481485130783764489)
      ·
        refine ⟨226592614861113848087823367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302123486481485130783764489 226592614861113848087823367)
        ·
          refine ⟨339888922291670772131735051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226592614861113848087823367 339888922291670772131735051)
          ·
            refine ⟨509833383437506158197602577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339888922291670772131735051 509833383437506158197602577)
            ·
              refine ⟨382375037578129618648201933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509833383437506158197602577 382375037578129618648201933)
              ·
                refine ⟨143390639091798606993075725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382375037578129618648201933 143390639091798606993075725)
                ·
                  refine ⟨53771489659424477622403397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143390639091798606993075725 53771489659424477622403397)
                  ·
                    refine ⟨10082154311142089554200637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53771489659424477622403397 10082154311142089554200637)
                    ·
                      refine ⟨3780807866678283582825239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10082154311142089554200637 3780807866678283582825239)
                      ·
                        rfl

theorem cell23_7363097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_7363097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363097 prefixEnd_7363097 := by exact prefixLift 7363097
  have htrace : WordTrace (prefixWord ++ tailWord_7363097) baseStart_7363097 baseEnd_7363097 := by
    simpa [prefixWord, tailWord_7363097, baseEnd_7363097] using wordTrace_append hprefix tailTrace_7363097
  have hstable : (prefixWord ++ tailWord_7363097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363097).length < 2 ^ (prefixWord ++ tailWord_7363097).sum := by decide
  have hdescent : baseEnd_7363097 < baseStart_7363097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363108 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_7363108 : Nat := 118140960795 + 7363108 * 2 ^ 59
def prefixEnd_7363108 : Nat := 4983230072969 + 3 ^ 40 * 7363108 * 2
def baseEnd_7363108 : Nat := 1260271171655161013262563

theorem tailTrace_7363108 : CollatzResearch.WordTrace tailWord_7363108 prefixEnd_7363108 1260271171655161013262563 := by
  unfold tailWord_7363108
  simp only [CollatzResearch.WordTrace]
  refine ⟨134277305704362354787664989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179036407605816473050219985 134277305704362354787664989)
  ·
    refine ⟨50353989639135883045374371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134277305704362354787664989 50353989639135883045374371)
    ·
      refine ⟨75530984458703824568061557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50353989639135883045374371 75530984458703824568061557)
      ·
        refine ⟨7081029793003483553255771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75530984458703824568061557 7081029793003483553255771)
        ·
          refine ⟨10621544689505225329883657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7081029793003483553255771 10621544689505225329883657)
          ·
            refine ⟨7966158517128918997412743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10621544689505225329883657 7966158517128918997412743)
            ·
              refine ⟨11949237775693378496119115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7966158517128918997412743 11949237775693378496119115)
              ·
                refine ⟨17923856663540067744178673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11949237775693378496119115 17923856663540067744178673)
                ·
                  refine ⟨13442892497655050808134005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17923856663540067744178673 13442892497655050808134005)
                  ·
                    refine ⟨1260271171655161013262563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13442892497655050808134005 1260271171655161013262563)
                    ·
                      rfl

theorem cell23_7363108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_7363108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363108 prefixEnd_7363108 := by exact prefixLift 7363108
  have htrace : WordTrace (prefixWord ++ tailWord_7363108) baseStart_7363108 baseEnd_7363108 := by
    simpa [prefixWord, tailWord_7363108, baseEnd_7363108] using wordTrace_append hprefix tailTrace_7363108
  have hstable : (prefixWord ++ tailWord_7363108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363108).length < 2 ^ (prefixWord ++ tailWord_7363108).sum := by decide
  have hdescent : baseEnd_7363108 < baseStart_7363108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363121 : List Nat := [1, 2, 2, 3, 1, 1, 3, 5, 1, 4]
def baseStart_7363121 : Nat := 118140960795 + 7363121 * 2 ^ 59
def prefixEnd_7363121 : Nat := 4983230072969 + 3 ^ 40 * 7363121 * 2
def baseEnd_7363121 : Nat := 1260273396737997162975043

theorem tailTrace_7363121 : CollatzResearch.WordTrace tailWord_7363121 prefixEnd_7363121 1260273396737997162975043 := by
  unfold tailWord_7363121
  simp only [CollatzResearch.WordTrace]
  refine ⟨268555085557677612795553217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179036723705118408530368811 268555085557677612795553217)
  ·
    refine ⟨201416314168258209596664913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268555085557677612795553217 201416314168258209596664913)
    ·
      refine ⟨151062235626193657197498685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201416314168258209596664913 151062235626193657197498685)
      ·
        refine ⟨56648338359822621449062007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151062235626193657197498685 56648338359822621449062007)
        ·
          refine ⟨84972507539733932173593011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56648338359822621449062007 84972507539733932173593011)
          ·
            refine ⟨127458761309600898260389517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84972507539733932173593011 127458761309600898260389517)
            ·
              refine ⟨47797035491100336847646069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127458761309600898260389517 47797035491100336847646069)
              ·
                refine ⟨4480972077290656579466819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47797035491100336847646069 4480972077290656579466819)
                ·
                  refine ⟨6721458115935984869200229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480972077290656579466819 6721458115935984869200229)
                  ·
                    refine ⟨1260273396737997162975043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6721458115935984869200229 1260273396737997162975043)
                    ·
                      rfl

theorem cell23_7363121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_7363121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363121 prefixEnd_7363121 := by exact prefixLift 7363121
  have htrace : WordTrace (prefixWord ++ tailWord_7363121) baseStart_7363121 baseEnd_7363121 := by
    simpa [prefixWord, tailWord_7363121, baseEnd_7363121] using wordTrace_append hprefix tailTrace_7363121
  have hstable : (prefixWord ++ tailWord_7363121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363121).length < 2 ^ (prefixWord ++ tailWord_7363121).sum := by decide
  have hdescent : baseEnd_7363121 < baseStart_7363121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363147 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 5, 5]
def baseStart_7363147 : Nat := 118140960795 + 7363147 * 2 ^ 59
def prefixEnd_7363147 : Nat := 4983230072969 + 3 ^ 40 * 7363147 * 2
def baseEnd_7363147 : Nat := 1260277846903669462400003

theorem tailTrace_7363147 : CollatzResearch.WordTrace tailWord_7363147 prefixEnd_7363147 1260277846903669462400003 := by
  unfold tailWord_7363147
  simp only [CollatzResearch.WordTrace]
  refine ⟨268556033855583419235999695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179037355903722279490666463 268556033855583419235999695)
  ·
    refine ⟨402834050783375128853999543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268556033855583419235999695 402834050783375128853999543)
    ·
      refine ⟨604251076175062693280999315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402834050783375128853999543 604251076175062693280999315)
      ·
        refine ⟨906376614262594039921498973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604251076175062693280999315 906376614262594039921498973)
        ·
          refine ⟨339891230348472764970562115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 906376614262594039921498973 339891230348472764970562115)
          ·
            refine ⟨509836845522709147455843173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339891230348472764970562115 509836845522709147455843173)
            ·
              refine ⟨95594408535507965147970595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 509836845522709147455843173 95594408535507965147970595)
              ·
                refine ⟨143391612803261947721955893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95594408535507965147970595 143391612803261947721955893)
                ·
                  refine ⟨13442963700305807598933365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143391612803261947721955893 13442963700305807598933365)
                  ·
                    refine ⟨1260277846903669462400003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13442963700305807598933365 1260277846903669462400003)
                    ·
                      rfl

theorem cell23_7363147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 5].length) (baseStart_7363147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363147 prefixEnd_7363147 := by exact prefixLift 7363147
  have htrace : WordTrace (prefixWord ++ tailWord_7363147) baseStart_7363147 baseEnd_7363147 := by
    simpa [prefixWord, tailWord_7363147, baseEnd_7363147] using wordTrace_append hprefix tailTrace_7363147
  have hstable : (prefixWord ++ tailWord_7363147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363147).length < 2 ^ (prefixWord ++ tailWord_7363147).sum := by decide
  have hdescent : baseEnd_7363147 < baseStart_7363147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363157 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_7363157 : Nat := 118140960795 + 7363157 * 2 ^ 59
def prefixEnd_7363157 : Nat := 4983230072969 + 3 ^ 40 * 7363157 * 2
def baseEnd_7363157 : Nat := 3780838675517553348074963

theorem tailTrace_7363157 : CollatzResearch.WordTrace tailWord_7363157 prefixEnd_7363157 3780838675517553348074963 := by
  unfold tailWord_7363157
  simp only [CollatzResearch.WordTrace]
  refine ⟨268556398585547190943863725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179037599057031460629242483 268556398585547190943863725)
  ·
    refine ⟨100708649469580196603948897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268556398585547190943863725 100708649469580196603948897)
    ·
      refine ⟨75531487102185147452961673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100708649469580196603948897 75531487102185147452961673)
      ·
        refine ⟨56648615326638860589721255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75531487102185147452961673 56648615326638860589721255)
        ·
          refine ⟨84972922989958290884581883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56648615326638860589721255 84972922989958290884581883)
          ·
            refine ⟨127459384484937436326872825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84972922989958290884581883 127459384484937436326872825)
            ·
              refine ⟨95594538363703077245154619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127459384484937436326872825 95594538363703077245154619)
              ·
                refine ⟨143391807545554615867731929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95594538363703077245154619 143391807545554615867731929)
                ·
                  refine ⟨107543855659165961900798947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143391807545554615867731929 107543855659165961900798947)
                  ·
                    refine ⟨161315783488748942851198421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107543855659165961900798947 161315783488748942851198421)
                    ·
                      refine ⟨3780838675517553348074963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161315783488748942851198421 3780838675517553348074963)
                      ·
                        rfl

theorem cell23_7363157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_7363157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363157 prefixEnd_7363157 := by exact prefixLift 7363157
  have htrace : WordTrace (prefixWord ++ tailWord_7363157) baseStart_7363157 baseEnd_7363157 := by
    simpa [prefixWord, tailWord_7363157, baseEnd_7363157] using wordTrace_append hprefix tailTrace_7363157
  have hstable : (prefixWord ++ tailWord_7363157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363157).length < 2 ^ (prefixWord ++ tailWord_7363157).sum := by decide
  have hdescent : baseEnd_7363157 < baseStart_7363157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363167 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 4]
def baseStart_7363167 : Nat := 118140960795 + 7363167 * 2 ^ 59
def prefixEnd_7363167 : Nat := 4983230072969 + 3 ^ 40 * 7363167 * 2
def baseEnd_7363167 : Nat := 3780843810324098308949917

theorem tailTrace_7363167 : CollatzResearch.WordTrace tailWord_7363167 prefixEnd_7363167 3780843810324098308949917 := by
  unfold tailWord_7363167
  simp only [CollatzResearch.WordTrace]
  refine ⟨268556763315510962651727755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179037842210340641767818503 268556763315510962651727755)
  ·
    refine ⟨402835144973266443977591633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268556763315510962651727755 402835144973266443977591633)
    ·
      refine ⟨302126358729949832983193725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402835144973266443977591633 302126358729949832983193725)
      ·
        refine ⟨113297384523731187368697647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302126358729949832983193725 113297384523731187368697647)
        ·
          refine ⟨169946076785596781053046471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113297384523731187368697647 169946076785596781053046471)
          ·
            refine ⟨254919115178395171579569707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169946076785596781053046471 254919115178395171579569707)
            ·
              refine ⟨382378672767592757369354561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254919115178395171579569707 382378672767592757369354561)
              ·
                refine ⟨286784004575694568027015921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382378672767592757369354561 286784004575694568027015921)
                ·
                  refine ⟨215088003431770926020261941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286784004575694568027015921 215088003431770926020261941)
                  ·
                    refine ⟨20164500321728524314399557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 215088003431770926020261941 20164500321728524314399557)
                    ·
                      refine ⟨3780843810324098308949917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20164500321728524314399557 3780843810324098308949917)
                      ·
                        rfl

theorem cell23_7363167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_7363167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363167 prefixEnd_7363167 := by exact prefixLift 7363167
  have htrace : WordTrace (prefixWord ++ tailWord_7363167) baseStart_7363167 baseEnd_7363167 := by
    simpa [prefixWord, tailWord_7363167, baseEnd_7363167] using wordTrace_append hprefix tailTrace_7363167
  have hstable : (prefixWord ++ tailWord_7363167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363167).length < 2 ^ (prefixWord ++ tailWord_7363167).sum := by decide
  have hdescent : baseEnd_7363167 < baseStart_7363167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363171 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 2, 3, 2]
def baseStart_7363171 : Nat := 118140960795 + 7363171 * 2 ^ 59
def prefixEnd_7363171 : Nat := 4983230072969 + 3 ^ 40 * 7363171 * 2
def baseEnd_7363171 : Nat := 3780845864246716293299899

theorem tailTrace_7363171 : CollatzResearch.WordTrace tailWord_7363171 prefixEnd_7363171 3780845864246716293299899 := by
  unfold tailWord_7363171
  simp only [CollatzResearch.WordTrace]
  refine ⟨268556909207496471334873367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179037939471664314223248911 268556909207496471334873367)
  ·
    refine ⟨402835363811244707002310051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268556909207496471334873367 402835363811244707002310051)
    ·
      refine ⟨604253045716867060503465077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402835363811244707002310051 604253045716867060503465077)
      ·
        refine ⟨56648723035956286922199851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 604253045716867060503465077 56648723035956286922199851)
        ·
          refine ⟨84973084553934430383299777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56648723035956286922199851 84973084553934430383299777)
          ·
            refine ⟨63729813415450822787474833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84973084553934430383299777 63729813415450822787474833)
            ·
              refine ⟨47797360061588117090606125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63729813415450822787474833 47797360061588117090606125)
              ·
                refine ⟨17924010023095543908977297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47797360061588117090606125 17924010023095543908977297)
                ·
                  refine ⟨13443007517321657931732973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17924010023095543908977297 13443007517321657931732973)
                  ·
                    refine ⟨5041127818995621724399865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13443007517321657931732973 5041127818995621724399865)
                    ·
                      refine ⟨3780845864246716293299899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5041127818995621724399865 3780845864246716293299899)
                      ·
                        rfl

theorem cell23_7363171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_7363171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363171 prefixEnd_7363171 := by exact prefixLift 7363171
  have htrace : WordTrace (prefixWord ++ tailWord_7363171) baseStart_7363171 baseEnd_7363171 := by
    simpa [prefixWord, tailWord_7363171, baseEnd_7363171] using wordTrace_append hprefix tailTrace_7363171
  have hstable : (prefixWord ++ tailWord_7363171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363171).length < 2 ^ (prefixWord ++ tailWord_7363171).sum := by decide
  have hdescent : baseEnd_7363171 < baseStart_7363171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363177 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 3, 6]
def baseStart_7363177 : Nat := 118140960795 + 7363177 * 2 ^ 59
def prefixEnd_7363177 : Nat := 4983230072969 + 3 ^ 40 * 7363177 * 2
def baseEnd_7363177 : Nat := 1260282981710214423274957

theorem tailTrace_7363177 : CollatzResearch.WordTrace tailWord_7363177 prefixEnd_7363177 1260282981710214423274957 := by
  unfold tailWord_7363177
  simp only [CollatzResearch.WordTrace]
  refine ⟨268557128045474734359591785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179038085363649822906394523 268557128045474734359591785)
  ·
    refine ⟨201417846034106050769693839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268557128045474734359591785 201417846034106050769693839)
    ·
      refine ⟨302126769051159076154540759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201417846034106050769693839 302126769051159076154540759)
      ·
        refine ⟨453190153576738614231811139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302126769051159076154540759 453190153576738614231811139)
        ·
          refine ⟨679785230365107921347716709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453190153576738614231811139 679785230365107921347716709)
          ·
            refine ⟨127459730693457735252696883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 679785230365107921347716709 127459730693457735252696883)
            ·
              refine ⟨191189596040186602879045325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127459730693457735252696883 191189596040186602879045325)
              ·
                refine ⟨71696098515069976079641997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191189596040186602879045325 71696098515069976079641997)
                ·
                  refine ⟨26886036943151241029865749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71696098515069976079641997 26886036943151241029865749)
                  ·
                    refine ⟨1260282981710214423274957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26886036943151241029865749 1260282981710214423274957)
                    ·
                      rfl

theorem cell23_7363177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 6].length) (baseStart_7363177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363177 prefixEnd_7363177 := by exact prefixLift 7363177
  have htrace : WordTrace (prefixWord ++ tailWord_7363177) baseStart_7363177 baseEnd_7363177 := by
    simpa [prefixWord, tailWord_7363177, baseEnd_7363177] using wordTrace_append hprefix tailTrace_7363177
  have hstable : (prefixWord ++ tailWord_7363177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363177).length < 2 ^ (prefixWord ++ tailWord_7363177).sum := by decide
  have hdescent : baseEnd_7363177 < baseStart_7363177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363181 : List Nat := [1, 5, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_7363181 : Nat := 118140960795 + 7363181 * 2 ^ 59
def prefixEnd_7363181 : Nat := 4983230072969 + 3 ^ 40 * 7363181 * 2
def baseEnd_7363181 : Nat := 1260283666351087084724951

theorem tailTrace_7363181 : CollatzResearch.WordTrace tailWord_7363181 prefixEnd_7363181 1260283666351087084724951 := by
  unfold tailWord_7363181
  simp only [CollatzResearch.WordTrace]
  refine ⟨268557273937460243042737397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179038182624973495361824931 268557273937460243042737397)
  ·
    refine ⟨25177244431636897785256631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268557273937460243042737397 25177244431636897785256631)
    ·
      refine ⟨37765866647455346677884947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25177244431636897785256631 37765866647455346677884947)
      ·
        refine ⟨56648799971183020016827421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37765866647455346677884947 56648799971183020016827421)
        ·
          refine ⟨21243299989193632506310283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56648799971183020016827421 21243299989193632506310283)
          ·
            refine ⟨31864949983790448759465425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21243299989193632506310283 31864949983790448759465425)
            ·
              refine ⟨23898712487842836569599069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31864949983790448759465425 23898712487842836569599069)
              ·
                refine ⟨8962017182941063713599651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23898712487842836569599069 8962017182941063713599651)
                ·
                  refine ⟨13443025774411595570399477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8962017182941063713599651 13443025774411595570399477)
                  ·
                    refine ⟨1260283666351087084724951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13443025774411595570399477 1260283666351087084724951)
                    ·
                      rfl

theorem cell23_7363181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_7363181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363181 prefixEnd_7363181 := by exact prefixLift 7363181
  have htrace : WordTrace (prefixWord ++ tailWord_7363181) baseStart_7363181 baseEnd_7363181 := by
    simpa [prefixWord, tailWord_7363181, baseEnd_7363181] using wordTrace_append hprefix tailTrace_7363181
  have hstable : (prefixWord ++ tailWord_7363181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363181).length < 2 ^ (prefixWord ++ tailWord_7363181).sum := by decide
  have hdescent : baseEnd_7363181 < baseStart_7363181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363214 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_7363214 : Nat := 118140960795 + 7363214 * 2 ^ 59
def prefixEnd_7363214 : Nat := 4983230072969 + 3 ^ 40 * 7363214 * 2
def baseEnd_7363214 : Nat := 3780867943914859625062201

theorem tailTrace_7363214 : CollatzResearch.WordTrace tailWord_7363214 prefixEnd_7363214 3780867943914859625062201 := by
  unfold tailWord_7363214
  simp only [CollatzResearch.WordTrace]
  refine ⟨33569809693292586209836087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179038985030893793119125797 33569809693292586209836087)
  ·
    refine ⟨50354714539938879314754131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33569809693292586209836087 50354714539938879314754131)
    ·
      refine ⟨75532071809908318972131197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50354714539938879314754131 75532071809908318972131197)
      ·
        refine ⟨28324526928715619614549199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75532071809908318972131197 28324526928715619614549199)
        ·
          refine ⟨42486790393073429421823799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28324526928715619614549199 42486790393073429421823799)
          ·
            refine ⟨63730185589610144132735699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42486790393073429421823799 63730185589610144132735699)
            ·
              refine ⟨95595278384415216199103549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63730185589610144132735699 95595278384415216199103549)
              ·
                refine ⟨35848229394155706074663831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95595278384415216199103549 35848229394155706074663831)
                ·
                  refine ⟨53772344091233559111995747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35848229394155706074663831 53772344091233559111995747)
                  ·
                    refine ⟨80658516136850338667993621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53772344091233559111995747 80658516136850338667993621)
                    ·
                      refine ⟨3780867943914859625062201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80658516136850338667993621 3780867943914859625062201)
                      ·
                        rfl

theorem cell23_7363214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_7363214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363214 prefixEnd_7363214 := by exact prefixLift 7363214
  have htrace : WordTrace (prefixWord ++ tailWord_7363214) baseStart_7363214 baseEnd_7363214 := by
    simpa [prefixWord, tailWord_7363214, baseEnd_7363214] using wordTrace_append hprefix tailTrace_7363214
  have hstable : (prefixWord ++ tailWord_7363214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363214).length < 2 ^ (prefixWord ++ tailWord_7363214).sum := by decide
  have hdescent : baseEnd_7363214 < baseStart_7363214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363218 : List Nat := [3, 2, 3, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_7363218 : Nat := 118140960795 + 7363218 * 2 ^ 59
def prefixEnd_7363218 : Nat := 4983230072969 + 3 ^ 40 * 7363218 * 2
def baseEnd_7363218 : Nat := 3780869997837477609412183

theorem tailTrace_7363218 : CollatzResearch.WordTrace tailWord_7363218 prefixEnd_7363218 3780869997837477609412183 := by
  unfold tailWord_7363218
  simp only [CollatzResearch.WordTrace]
  refine ⟨67139655859581549590458577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179039082292217465574556205 67139655859581549590458577)
  ·
    refine ⟨50354741894686162192843933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67139655859581549590458577 50354741894686162192843933)
    ·
      refine ⟨18883028210507310822316475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50354741894686162192843933 18883028210507310822316475)
      ·
        refine ⟨28324542315760966233474713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18883028210507310822316475 28324542315760966233474713)
        ·
          refine ⟨21243406736820724675106035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28324542315760966233474713 21243406736820724675106035)
          ·
            refine ⟨31865110105231087012659053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21243406736820724675106035 31865110105231087012659053)
            ·
              refine ⟨11949416289461657629747145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31865110105231087012659053 11949416289461657629747145)
              ·
                refine ⟨8962062217096243222310359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11949416289461657629747145 8962062217096243222310359)
                ·
                  refine ⟨13443093325644364833465539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8962062217096243222310359 13443093325644364833465539)
                  ·
                    refine ⟨20164639988466547250198309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13443093325644364833465539 20164639988466547250198309)
                    ·
                      refine ⟨3780869997837477609412183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20164639988466547250198309 3780869997837477609412183)
                      ·
                        rfl

theorem cell23_7363218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_7363218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363218 prefixEnd_7363218 := by exact prefixLift 7363218
  have htrace : WordTrace (prefixWord ++ tailWord_7363218) baseStart_7363218 baseEnd_7363218 := by
    simpa [prefixWord, tailWord_7363218, baseEnd_7363218] using wordTrace_append hprefix tailTrace_7363218
  have hstable : (prefixWord ++ tailWord_7363218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363218).length < 2 ^ (prefixWord ++ tailWord_7363218).sum := by decide
  have hdescent : baseEnd_7363218 < baseStart_7363218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363265 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7363265 : Nat := 118140960795 + 7363265 * 2 ^ 59
def prefixEnd_7363265 : Nat := 4983230072969 + 3 ^ 40 * 7363265 * 2
def baseEnd_7363265 : Nat := 3780894131428238925524467

theorem tailTrace_7363265 : CollatzResearch.WordTrace tailWord_7363265 prefixEnd_7363265 3780894131428238925524467 := by
  unfold tailWord_7363265
  simp only [CollatzResearch.WordTrace]
  refine ⟨268560337669155925388795249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179040225112770616925863499 268560337669155925388795249)
  ·
    refine ⟨201420253251866944041596437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268560337669155925388795249 201420253251866944041596437)
    ·
      refine ⟨9441574371181263001949833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 201420253251866944041596437 9441574371181263001949833)
      ·
        refine ⟨7081180778385947251462375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9441574371181263001949833 7081180778385947251462375)
        ·
          refine ⟨10621771167578920877193563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7081180778385947251462375 10621771167578920877193563)
          ·
            refine ⟨15932656751368381315790345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10621771167578920877193563 15932656751368381315790345)
            ·
              refine ⟨11949492563526285986842759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15932656751368381315790345 11949492563526285986842759)
              ·
                refine ⟨17924238845289428980264139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11949492563526285986842759 17924238845289428980264139)
                ·
                  refine ⟨26886358267934143470396209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17924238845289428980264139 26886358267934143470396209)
                  ·
                    refine ⟨20164768700950607602797157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26886358267934143470396209 20164768700950607602797157)
                    ·
                      refine ⟨3780894131428238925524467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20164768700950607602797157 3780894131428238925524467)
                      ·
                        rfl

theorem cell23_7363265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7363265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363265 prefixEnd_7363265 := by exact prefixLift 7363265
  have htrace : WordTrace (prefixWord ++ tailWord_7363265) baseStart_7363265 baseEnd_7363265 := by
    simpa [prefixWord, tailWord_7363265, baseEnd_7363265] using wordTrace_append hprefix tailTrace_7363265
  have hstable : (prefixWord ++ tailWord_7363265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363265).length < 2 ^ (prefixWord ++ tailWord_7363265).sum := by decide
  have hdescent : baseEnd_7363265 < baseStart_7363265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363268 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_7363268 : Nat := 118140960795 + 7363268 * 2 ^ 59
def prefixEnd_7363268 : Nat := 4983230072969 + 3 ^ 40 * 7363268 * 2
def baseEnd_7363268 : Nat := 3780895671870202413786953

theorem tailTrace_7363268 : CollatzResearch.WordTrace tailWord_7363268 prefixEnd_7363268 3780895671870202413786953 := by
  unfold tailWord_7363268
  simp only [CollatzResearch.WordTrace]
  refine ⟨134280223544072528450577229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179040298058763371267436305 134280223544072528450577229)
  ·
    refine ⟨50355083829027198168966461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134280223544072528450577229 50355083829027198168966461)
    ·
      refine ⟨18883156435885199313362423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50355083829027198168966461 18883156435885199313362423)
      ·
        refine ⟨28324734653827798970043635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18883156435885199313362423 28324734653827798970043635)
        ·
          refine ⟨42487101980741698455065453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28324734653827798970043635 42487101980741698455065453)
          ·
            refine ⟨15932663242778136920649545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42487101980741698455065453 15932663242778136920649545)
            ·
              refine ⟨11949497432083602690487159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15932663242778136920649545 11949497432083602690487159)
              ·
                refine ⟨17924246148125404035730739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11949497432083602690487159 17924246148125404035730739)
                ·
                  refine ⟨26886369222188106053596109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17924246148125404035730739 26886369222188106053596109)
                  ·
                    refine ⟨10082388458320539770098541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26886369222188106053596109 10082388458320539770098541)
                    ·
                      refine ⟨3780895671870202413786953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10082388458320539770098541 3780895671870202413786953)
                      ·
                        rfl

theorem cell23_7363268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_7363268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363268 prefixEnd_7363268 := by exact prefixLift 7363268
  have htrace : WordTrace (prefixWord ++ tailWord_7363268) baseStart_7363268 baseEnd_7363268 := by
    simpa [prefixWord, tailWord_7363268, baseEnd_7363268] using wordTrace_append hprefix tailTrace_7363268
  have hstable : (prefixWord ++ tailWord_7363268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363268).length < 2 ^ (prefixWord ++ tailWord_7363268).sum := by decide
  have hdescent : baseEnd_7363268 < baseStart_7363268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363278 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2]
def baseStart_7363278 : Nat := 118140960795 + 7363278 * 2 ^ 59
def prefixEnd_7363278 : Nat := 4983230072969 + 3 ^ 40 * 7363278 * 2
def baseEnd_7363278 : Nat := 3780900806676747374661907

theorem tailTrace_7363278 : CollatzResearch.WordTrace tailWord_7363278 prefixEnd_7363278 3780900806676747374661907 := by
  unfold tailWord_7363278
  simp only [CollatzResearch.WordTrace]
  refine ⟨33570101477263603576127311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179040541212072552406012325 33570101477263603576127311)
  ·
    refine ⟨50355152215895405364190967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33570101477263603576127311 50355152215895405364190967)
    ·
      refine ⟨75532728323843108046286451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50355152215895405364190967 75532728323843108046286451)
      ·
        refine ⟨113299092485764662069429677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75532728323843108046286451 113299092485764662069429677)
        ·
          refine ⟨42487159682161748276036129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113299092485764662069429677 42487159682161748276036129)
          ·
            refine ⟨31865369761621311207027097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42487159682161748276036129 31865369761621311207027097)
            ·
              refine ⟨23899027321215983405270323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31865369761621311207027097 23899027321215983405270323)
              ·
                refine ⟨35848540981823975107905485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23899027321215983405270323 35848540981823975107905485)
                ·
                  refine ⟨13443202868183990665464557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35848540981823975107905485 13443202868183990665464557)
                  ·
                    refine ⟨5041201075568996499549209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13443202868183990665464557 5041201075568996499549209)
                    ·
                      refine ⟨3780900806676747374661907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5041201075568996499549209 3780900806676747374661907)
                      ·
                        rfl

theorem cell23_7363278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_7363278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363278 prefixEnd_7363278 := by exact prefixLift 7363278
  have htrace : WordTrace (prefixWord ++ tailWord_7363278) baseStart_7363278 baseEnd_7363278 := by
    simpa [prefixWord, tailWord_7363278, baseEnd_7363278] using wordTrace_append hprefix tailTrace_7363278
  have hstable : (prefixWord ++ tailWord_7363278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363278).length < 2 ^ (prefixWord ++ tailWord_7363278).sum := by decide
  have hdescent : baseEnd_7363278 < baseStart_7363278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363295 : List Nat := [1, 1, 2, 3, 2, 3, 4, 1, 1, 3, 2]
def baseStart_7363295 : Nat := 118140960795 + 7363295 * 2 ^ 59
def prefixEnd_7363295 : Nat := 4983230072969 + 3 ^ 40 * 7363295 * 2
def baseEnd_7363295 : Nat := 3780909535847873808149329

theorem tailTrace_7363295 : CollatzResearch.WordTrace tailWord_7363295 prefixEnd_7363295 3780909535847873808149329 := by
  unfold tailWord_7363295
  simp only [CollatzResearch.WordTrace]
  refine ⟨268561431859047240512387339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179040954572698160341591559 268561431859047240512387339)
  ·
    refine ⟨402842147788570860768581009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268561431859047240512387339 402842147788570860768581009)
    ·
      refine ⟨302131610841428145576435757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402842147788570860768581009 302131610841428145576435757)
      ·
        refine ⟨113299354065535554591163409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302131610841428145576435757 113299354065535554591163409)
        ·
          refine ⟨84974515549151665943372557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113299354065535554591163409 84974515549151665943372557)
          ·
            refine ⟨31865443330931874728764709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84974515549151665943372557 31865443330931874728764709)
            ·
              refine ⟨5974770624549726511643383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31865443330931874728764709 5974770624549726511643383)
              ·
                refine ⟨8962155936824589767465075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5974770624549726511643383 8962155936824589767465075)
                ·
                  refine ⟨13443233905236884651197613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8962155936824589767465075 13443233905236884651197613)
                  ·
                    refine ⟨5041212714463831744199105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13443233905236884651197613 5041212714463831744199105)
                    ·
                      refine ⟨3780909535847873808149329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5041212714463831744199105 3780909535847873808149329)
                      ·
                        rfl

theorem cell23_7363295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_7363295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363295 prefixEnd_7363295 := by exact prefixLift 7363295
  have htrace : WordTrace (prefixWord ++ tailWord_7363295) baseStart_7363295 baseEnd_7363295 := by
    simpa [prefixWord, tailWord_7363295, baseEnd_7363295] using wordTrace_append hprefix tailTrace_7363295
  have hstable : (prefixWord ++ tailWord_7363295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363295).length < 2 ^ (prefixWord ++ tailWord_7363295).sum := by decide
  have hdescent : baseEnd_7363295 < baseStart_7363295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363361 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 2, 5]
def baseStart_7363361 : Nat := 118140960795 + 7363361 * 2 ^ 59
def prefixEnd_7363361 : Nat := 4983230072969 + 3 ^ 40 * 7363361 * 2
def baseEnd_7363361 : Nat := 1260314475190356849974675

theorem tailTrace_7363361 : CollatzResearch.WordTrace tailWord_7363361 prefixEnd_7363361 1260314475190356849974675 := by
  unfold tailWord_7363361
  simp only [CollatzResearch.WordTrace]
  refine ⟨268563839076808133784289937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179042559384538755856193291 268563839076808133784289937)
  ·
    refine ⟨201422879307606100338217453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268563839076808133784289937 201422879307606100338217453)
    ·
      refine ⟨75533579740352287626831545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201422879307606100338217453 75533579740352287626831545)
      ·
        refine ⟨56650184805264215720123659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75533579740352287626831545 56650184805264215720123659)
        ·
          refine ⟨84975277207896323580185489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56650184805264215720123659 84975277207896323580185489)
          ·
            refine ⟨63731457905922242685139117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84975277207896323580185489 63731457905922242685139117)
            ·
              refine ⟨23899296714720841006927169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63731457905922242685139117 23899296714720841006927169)
              ·
                refine ⟨17924472536040630755195377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23899296714720841006927169 17924472536040630755195377)
                ·
                  refine ⟨13443354402030473066396533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17924472536040630755195377 13443354402030473066396533)
                  ·
                    refine ⟨1260314475190356849974675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13443354402030473066396533 1260314475190356849974675)
                    ·
                      rfl

theorem cell23_7363361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_7363361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363361 prefixEnd_7363361 := by exact prefixLift 7363361
  have htrace : WordTrace (prefixWord ++ tailWord_7363361) baseStart_7363361 baseEnd_7363361 := by
    simpa [prefixWord, tailWord_7363361, baseEnd_7363361] using wordTrace_append hprefix tailTrace_7363361
  have hstable : (prefixWord ++ tailWord_7363361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363361).length < 2 ^ (prefixWord ++ tailWord_7363361).sum := by decide
  have hdescent : baseEnd_7363361 < baseStart_7363361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363368 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_7363368 : Nat := 118140960795 + 7363368 * 2 ^ 59
def prefixEnd_7363368 : Nat := 4983230072969 + 3 ^ 40 * 7363368 * 2
def baseEnd_7363368 : Nat := 3780947019935652022536493

theorem tailTrace_7363368 : CollatzResearch.WordTrace tailWord_7363368 prefixEnd_7363368 3780947019935652022536493 := by
  unfold tailWord_7363368
  simp only [CollatzResearch.WordTrace]
  refine ⟨134282047193891386989897379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179042729591855182653196505 134282047193891386989897379)
  ·
    refine ⟨201423070790837080484846069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134282047193891386989897379 201423070790837080484846069)
    ·
      refine ⟨18883412886640976295454319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201423070790837080484846069 18883412886640976295454319)
      ·
        refine ⟨28325119329961464443181479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18883412886640976295454319 28325119329961464443181479)
        ·
          refine ⟨42487678994942196664772219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28325119329961464443181479 42487678994942196664772219)
          ·
            refine ⟨63731518492413294997158329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42487678994942196664772219 63731518492413294997158329)
            ·
              refine ⟨47798638869309971247868747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63731518492413294997158329 47798638869309971247868747)
              ·
                refine ⟨71697958303964956871803121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47798638869309971247868747 71697958303964956871803121)
                ·
                  refine ⟨53773468727973717653852341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71697958303964956871803121 53773468727973717653852341)
                  ·
                    refine ⟨5041262693247536030048657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53773468727973717653852341 5041262693247536030048657)
                    ·
                      refine ⟨3780947019935652022536493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5041262693247536030048657 3780947019935652022536493)
                      ·
                        rfl

theorem cell23_7363368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_7363368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363368 prefixEnd_7363368 := by exact prefixLift 7363368
  have htrace : WordTrace (prefixWord ++ tailWord_7363368) baseStart_7363368 baseEnd_7363368 := by
    simpa [prefixWord, tailWord_7363368, baseEnd_7363368] using wordTrace_append hprefix tailTrace_7363368
  have hstable : (prefixWord ++ tailWord_7363368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363368).length < 2 ^ (prefixWord ++ tailWord_7363368).sum := by decide
  have hdescent : baseEnd_7363368 < baseStart_7363368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363418 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3]
def baseStart_7363418 : Nat := 118140960795 + 7363418 * 2 ^ 59
def prefixEnd_7363418 : Nat := 4983230072969 + 3 ^ 40 * 7363418 * 2
def baseEnd_7363418 : Nat := 3780972693968376826911263

theorem tailTrace_7363418 : CollatzResearch.WordTrace tailWord_7363418 prefixEnd_7363418 3780972693968376826911263 := by
  unfold tailWord_7363418
  simp only [CollatzResearch.WordTrace]
  refine ⟨67141479509400408129778727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179043945358401088346076605 67141479509400408129778727)
  ·
    refine ⟨100712219264100612194668091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67141479509400408129778727 100712219264100612194668091)
    ·
      refine ⟨151068328896150918292002137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100712219264100612194668091 151068328896150918292002137)
      ·
        refine ⟨113301246672113188719001603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151068328896150918292002137 113301246672113188719001603)
        ·
          refine ⟨169951870008169783078502405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113301246672113188719001603 169951870008169783078502405)
          ·
            refine ⟨31865975626531834327219201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169951870008169783078502405 31865975626531834327219201)
            ·
              refine ⟨23899481719898875745414401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31865975626531834327219201 23899481719898875745414401)
              ·
                refine ⟨17924611289924156809060801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23899481719898875745414401 17924611289924156809060801)
                ·
                  refine ⟨13443458467443117606795601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17924611289924156809060801 13443458467443117606795601)
                  ·
                    refine ⟨10082593850582338205096701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13443458467443117606795601 10082593850582338205096701)
                    ·
                      refine ⟨3780972693968376826911263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10082593850582338205096701 3780972693968376826911263)
                      ·
                        rfl

theorem cell23_7363418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_7363418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363418 prefixEnd_7363418 := by exact prefixLift 7363418
  have htrace : WordTrace (prefixWord ++ tailWord_7363418) baseStart_7363418 baseEnd_7363418 := by
    simpa [prefixWord, tailWord_7363418, baseEnd_7363418] using wordTrace_append hprefix tailTrace_7363418
  have hstable : (prefixWord ++ tailWord_7363418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363418).length < 2 ^ (prefixWord ++ tailWord_7363418).sum := by decide
  have hdescent : baseEnd_7363418 < baseStart_7363418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363451 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 3, 5]
def baseStart_7363451 : Nat := 118140960795 + 7363451 * 2 ^ 59
def prefixEnd_7363451 : Nat := 4983230072969 + 3 ^ 40 * 7363451 * 2
def baseEnd_7363451 : Nat := 1260329879609991732599537

theorem tailTrace_7363451 : CollatzResearch.WordTrace tailWord_7363451 prefixEnd_7363451 1260329879609991732599537 := by
  unfold tailWord_7363451
  simp only [CollatzResearch.WordTrace]
  refine ⟨268567121646482079155066207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179044747764321386103377471 268567121646482079155066207)
  ·
    refine ⟨402850682469723118732599311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268567121646482079155066207 402850682469723118732599311)
    ·
      refine ⟨604276023704584678098898967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402850682469723118732599311 604276023704584678098898967)
      ·
        refine ⟨906414035556877017148348451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604276023704584678098898967 906414035556877017148348451)
        ·
          refine ⟨1359621053335315525722522677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906414035556877017148348451 1359621053335315525722522677)
          ·
            refine ⟨127464473750185830536486501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1359621053335315525722522677 127464473750185830536486501)
            ·
              refine ⟨23899588828159843225591219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127464473750185830536486501 23899588828159843225591219)
              ·
                refine ⟨35849383242239764838386829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23899588828159843225591219 35849383242239764838386829)
                ·
                  refine ⟨13443518715839911814395061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35849383242239764838386829 13443518715839911814395061)
                  ·
                    refine ⟨1260329879609991732599537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13443518715839911814395061 1260329879609991732599537)
                    ·
                      rfl

theorem cell23_7363451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 5].length) (baseStart_7363451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363451 prefixEnd_7363451 := by exact prefixLift 7363451
  have htrace : WordTrace (prefixWord ++ tailWord_7363451) baseStart_7363451 baseEnd_7363451 := by
    simpa [prefixWord, tailWord_7363451, baseEnd_7363451] using wordTrace_append hprefix tailTrace_7363451
  have hstable : (prefixWord ++ tailWord_7363451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363451).length < 2 ^ (prefixWord ++ tailWord_7363451).sum := by decide
  have hdescent : baseEnd_7363451 < baseStart_7363451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363482 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3]
def baseStart_7363482 : Nat := 118140960795 + 7363482 * 2 ^ 59
def prefixEnd_7363482 : Nat := 4983230072969 + 3 ^ 40 * 7363482 * 2
def baseEnd_7363482 : Nat := 3781005556730264576510969

theorem tailTrace_7363482 : CollatzResearch.WordTrace tailWord_7363482 prefixEnd_7363482 3781005556730264576510969 := by
  unfold tailWord_7363482
  simp only [CollatzResearch.WordTrace]
  refine ⟨67142063077342442862361175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179045501539579847632963133 67142063077342442862361175)
  ·
    refine ⟨100713094616013664293541763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67142063077342442862361175 100713094616013664293541763)
    ·
      refine ⟨151069641924020496440312645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100713094616013664293541763 151069641924020496440312645)
      ·
        refine ⟨28325557860753843082558621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151069641924020496440312645 28325557860753843082558621)
        ·
          refine ⟨10622084197782691155959483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28325557860753843082558621 10622084197782691155959483)
          ·
            refine ⟨15933126296674036733939225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10622084197782691155959483 15933126296674036733939225)
            ·
              refine ⟨11949844722505527550454419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15933126296674036733939225 11949844722505527550454419)
              ·
                refine ⟨17924767083758291325681629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11949844722505527550454419 17924767083758291325681629)
                ·
                  refine ⟨6721787656409359247130611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17924767083758291325681629 6721787656409359247130611)
                  ·
                    refine ⟨10082681484614038870695917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6721787656409359247130611 10082681484614038870695917)
                    ·
                      refine ⟨3781005556730264576510969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10082681484614038870695917 3781005556730264576510969)
                      ·
                        rfl

theorem cell23_7363482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_7363482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363482 prefixEnd_7363482 := by exact prefixLift 7363482
  have htrace : WordTrace (prefixWord ++ tailWord_7363482) baseStart_7363482 baseEnd_7363482 := by
    simpa [prefixWord, tailWord_7363482, baseEnd_7363482] using wordTrace_append hprefix tailTrace_7363482
  have hstable : (prefixWord ++ tailWord_7363482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363482).length < 2 ^ (prefixWord ++ tailWord_7363482).sum := by decide
  have hdescent : baseEnd_7363482 < baseStart_7363482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363491 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 5]
def baseStart_7363491 : Nat := 118140960795 + 7363491 * 2 ^ 59
def prefixEnd_7363491 : Nat := 4983230072969 + 3 ^ 40 * 7363491 * 2
def baseEnd_7363491 : Nat := 3781010178056155041298427

theorem tailTrace_7363491 : CollatzResearch.WordTrace tailWord_7363491 prefixEnd_7363491 3781010178056155041298427 := by
  unfold tailWord_7363491
  simp only [CollatzResearch.WordTrace]
  refine ⟨268568580566337165986522327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179045720377558110657681551 268568580566337165986522327)
  ·
    refine ⟨402852870849505748979783491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268568580566337165986522327 402852870849505748979783491)
    ·
      refine ⟨604279306274258623469675237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402852870849505748979783491 604279306274258623469675237)
      ·
        refine ⟨113302369926423491900564107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 604279306274258623469675237 113302369926423491900564107)
        ·
          refine ⟨169953554889635237850846161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113302369926423491900564107 169953554889635237850846161)
          ·
            refine ⟨127465166167226428388134621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169953554889635237850846161 127465166167226428388134621)
            ·
              refine ⟨47799437312709910645550483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127465166167226428388134621 47799437312709910645550483)
              ·
                refine ⟨71699155969064865968325725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47799437312709910645550483 71699155969064865968325725)
                ·
                  refine ⟨26887183488399324738122147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71699155969064865968325725 26887183488399324738122147)
                  ·
                    refine ⟨40330775232598987107183221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26887183488399324738122147 40330775232598987107183221)
                    ·
                      refine ⟨3781010178056155041298427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40330775232598987107183221 3781010178056155041298427)
                      ·
                        rfl

theorem cell23_7363491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_7363491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363491 prefixEnd_7363491 := by exact prefixLift 7363491
  have htrace : WordTrace (prefixWord ++ tailWord_7363491) baseStart_7363491 baseEnd_7363491 := by
    simpa [prefixWord, tailWord_7363491, baseEnd_7363491] using wordTrace_append hprefix tailTrace_7363491
  have hstable : (prefixWord ++ tailWord_7363491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363491).length < 2 ^ (prefixWord ++ tailWord_7363491).sum := by decide
  have hdescent : baseEnd_7363491 < baseStart_7363491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363510 : List Nat := [5, 1, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7363510 : Nat := 118140960795 + 7363510 * 2 ^ 59
def prefixEnd_7363510 : Nat := 4983230072969 + 3 ^ 40 * 7363510 * 2
def baseEnd_7363510 : Nat := 1260339978062863488986947

theorem tailTrace_7363510 : CollatzResearch.WordTrace tailWord_7363510 prefixEnd_7363510 1260339978062863488986947 := by
  unfold tailWord_7363510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16785579597079270764466499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179046182368845554820975989 16785579597079270764466499)
  ·
    refine ⟨25178369395618906146699749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16785579597079270764466499 25178369395618906146699749)
    ·
      refine ⟨4720944261678544902506203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25178369395618906146699749 4720944261678544902506203)
      ·
        refine ⟨7081416392517817353759305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4720944261678544902506203 7081416392517817353759305)
        ·
          refine ⟨5311062294388363015319479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7081416392517817353759305 5311062294388363015319479)
          ·
            refine ⟨7966593441582544522979219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5311062294388363015319479 7966593441582544522979219)
            ·
              refine ⟨11949890162373816784468829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7966593441582544522979219 11949890162373816784468829)
              ·
                refine ⟨4481208810890181294175811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11949890162373816784468829 4481208810890181294175811)
                ·
                  refine ⟨6721813216335271941263717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4481208810890181294175811 6721813216335271941263717)
                  ·
                    refine ⟨1260339978062863488986947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6721813216335271941263717 1260339978062863488986947)
                    ·
                      rfl

theorem cell23_7363510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7363510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363510 prefixEnd_7363510 := by exact prefixLift 7363510
  have htrace : WordTrace (prefixWord ++ tailWord_7363510) baseStart_7363510 baseEnd_7363510 := by
    simpa [prefixWord, tailWord_7363510, baseEnd_7363510] using wordTrace_append hprefix tailTrace_7363510
  have hstable : (prefixWord ++ tailWord_7363510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363510).length < 2 ^ (prefixWord ++ tailWord_7363510).sum := by decide
  have hdescent : baseEnd_7363510 < baseStart_7363510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363518 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_7363518 : Nat := 118140960795 + 7363518 * 2 ^ 59
def prefixEnd_7363518 : Nat := 4983230072969 + 3 ^ 40 * 7363518 * 2
def baseEnd_7363518 : Nat := 3781024042033826435660803

theorem tailTrace_7363518 : CollatzResearch.WordTrace tailWord_7363518 prefixEnd_7363518 3781024042033826435660803 := by
  unfold tailWord_7363518
  simp only [CollatzResearch.WordTrace]
  refine ⟨33571195667154918699719401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179046376891492899731836805 33571195667154918699719401)
  ·
    refine ⟨25178396750366189024789551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33571195667154918699719401 25178396750366189024789551)
    ·
      refine ⟨37767595125549283537184327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25178396750366189024789551 37767595125549283537184327)
      ·
        refine ⟨56651392688323925305776491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37767595125549283537184327 56651392688323925305776491)
        ·
          refine ⟨84977089032485887958664737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56651392688323925305776491 84977089032485887958664737)
          ·
            refine ⟨63732816774364415968998553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84977089032485887958664737 63732816774364415968998553)
            ·
              refine ⟨47799612580773311976748915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63732816774364415968998553 47799612580773311976748915)
              ·
                refine ⟨71699418871159967965123373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47799612580773311976748915 71699418871159967965123373)
                ·
                  refine ⟨26887282076684987986921265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71699418871159967965123373 26887282076684987986921265)
                  ·
                    refine ⟨20165461557513740990190949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26887282076684987986921265 20165461557513740990190949)
                    ·
                      refine ⟨3781024042033826435660803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20165461557513740990190949 3781024042033826435660803)
                      ·
                        rfl

theorem cell23_7363518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_7363518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363518 prefixEnd_7363518 := by exact prefixLift 7363518
  have htrace : WordTrace (prefixWord ++ tailWord_7363518) baseStart_7363518 baseEnd_7363518 := by
    simpa [prefixWord, tailWord_7363518, baseEnd_7363518] using wordTrace_append hprefix tailTrace_7363518
  have hstable : (prefixWord ++ tailWord_7363518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363518).length < 2 ^ (prefixWord ++ tailWord_7363518).sum := by decide
  have hdescent : baseEnd_7363518 < baseStart_7363518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363528 : List Nat := [2, 1, 3, 1, 5, 2, 9]
def baseStart_7363528 : Nat := 118140960795 + 7363528 * 2 ^ 59
def prefixEnd_7363528 : Nat := 4983230072969 + 3 ^ 40 * 7363528 * 2
def baseEnd_7363528 : Nat := 46679372553584832055997

theorem tailTrace_7363528 : CollatzResearch.WordTrace tailWord_7363528 prefixEnd_7363528 46679372553584832055997 := by
  unfold tailWord_7363528
  simp only [CollatzResearch.WordTrace]
  refine ⟨134284965033601560652809619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179046620044802080870412825 134284965033601560652809619)
  ·
    refine ⟨201427447550402340979214429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134284965033601560652809619 201427447550402340979214429)
    ·
      refine ⟨75535292831400877867205411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201427447550402340979214429 75535292831400877867205411)
      ·
        refine ⟨113302939247101316800808117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75535292831400877867205411 113302939247101316800808117)
        ·
          refine ⟨10622150554415748450075761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113302939247101316800808117 10622150554415748450075761)
          ·
            refine ⟨7966612915811811337556821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10622150554415748450075761 7966612915811811337556821)
            ·
              refine ⟨46679372553584832055997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7966612915811811337556821 46679372553584832055997)
              ·
                rfl

theorem cell23_7363528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 9].length) (baseStart_7363528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363528 prefixEnd_7363528 := by exact prefixLift 7363528
  have htrace : WordTrace (prefixWord ++ tailWord_7363528) baseStart_7363528 baseEnd_7363528 := by
    simpa [prefixWord, tailWord_7363528, baseEnd_7363528] using wordTrace_append hprefix tailTrace_7363528
  have hstable : (prefixWord ++ tailWord_7363528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363528).length < 2 ^ (prefixWord ++ tailWord_7363528).sum := by decide
  have hdescent : baseEnd_7363528 < baseStart_7363528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363533 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7363533 : Nat := 118140960795 + 7363533 * 2 ^ 59
def prefixEnd_7363533 : Nat := 4983230072969 + 3 ^ 40 * 7363533 * 2
def baseEnd_7363533 : Nat := 3781031744243643876973235

theorem tailTrace_7363533 : CollatzResearch.WordTrace tailWord_7363533 prefixEnd_7363533 3781031744243643876973235 := by
  unfold tailWord_7363533
  simp only [CollatzResearch.WordTrace]
  refine ⟨268570112432185007159551253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179046741621456671439700835 268570112432185007159551253)
  ·
    refine ⟨12589224020258672210603965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 268570112432185007159551253 12589224020258672210603965)
    ·
      refine ⟨4720959007597002078976487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12589224020258672210603965 4720959007597002078976487)
      ·
        refine ⟨7081438511395503118464731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4720959007597002078976487 7081438511395503118464731)
        ·
          refine ⟨10622157767093254677697097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7081438511395503118464731 10622157767093254677697097)
          ·
            refine ⟨7966618325319941008272823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10622157767093254677697097 7966618325319941008272823)
            ·
              refine ⟨11949927487979911512409235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7966618325319941008272823 11949927487979911512409235)
              ·
                refine ⟨17924891231969867268613853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11949927487979911512409235 17924891231969867268613853)
                ·
                  refine ⟨6721834211988700225730195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17924891231969867268613853 6721834211988700225730195)
                  ·
                    refine ⟨10082751317983050338595293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6721834211988700225730195 10082751317983050338595293)
                    ·
                      refine ⟨3781031744243643876973235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10082751317983050338595293 3781031744243643876973235)
                      ·
                        rfl

theorem cell23_7363533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7363533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363533 prefixEnd_7363533 := by exact prefixLift 7363533
  have htrace : WordTrace (prefixWord ++ tailWord_7363533) baseStart_7363533 baseEnd_7363533 := by
    simpa [prefixWord, tailWord_7363533, baseEnd_7363533] using wordTrace_append hprefix tailTrace_7363533
  have hstable : (prefixWord ++ tailWord_7363533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363533).length < 2 ^ (prefixWord ++ tailWord_7363533).sum := by decide
  have hdescent : baseEnd_7363533 < baseStart_7363533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363549 : List Nat := [1, 4, 3, 1, 2, 3, 2, 1, 2, 4]
def baseStart_7363549 : Nat := 118140960795 + 7363549 * 2 ^ 59
def prefixEnd_7363549 : Nat := 4983230072969 + 3 ^ 40 * 7363549 * 2
def baseEnd_7363549 : Nat := 1260346653311371938124387

theorem tailTrace_7363549 : CollatzResearch.WordTrace tailWord_7363549 prefixEnd_7363549 1260346653311371938124387 := by
  unfold tailWord_7363549
  simp only [CollatzResearch.WordTrace]
  refine ⟨268570696000127041892133701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179047130666751361261422467 268570696000127041892133701)
  ·
    refine ⟨50357005500023820354775069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268570696000127041892133701 50357005500023820354775069)
    ·
      refine ⟨18883877062508932633040651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50357005500023820354775069 18883877062508932633040651)
      ·
        refine ⟨28325815593763398949560977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18883877062508932633040651 28325815593763398949560977)
        ·
          refine ⟨21244361695322549212170733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28325815593763398949560977 21244361695322549212170733)
          ·
            refine ⟨7966635635745955954564025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21244361695322549212170733 7966635635745955954564025)
            ·
              refine ⟨5974976726809466965923019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7966635635745955954564025 5974976726809466965923019)
              ·
                refine ⟨8962465090214200448884529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5974976726809466965923019 8962465090214200448884529)
                ·
                  refine ⟨6721848817660650336663397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8962465090214200448884529 6721848817660650336663397)
                  ·
                    refine ⟨1260346653311371938124387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6721848817660650336663397 1260346653311371938124387)
                    ·
                      rfl

theorem cell23_7363549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_7363549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363549 prefixEnd_7363549 := by exact prefixLift 7363549
  have htrace : WordTrace (prefixWord ++ tailWord_7363549) baseStart_7363549 baseEnd_7363549 := by
    simpa [prefixWord, tailWord_7363549, baseEnd_7363549] using wordTrace_append hprefix tailTrace_7363549
  have hstable : (prefixWord ++ tailWord_7363549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363549).length < 2 ^ (prefixWord ++ tailWord_7363549).sum := by decide
  have hdescent : baseEnd_7363549 < baseStart_7363549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
