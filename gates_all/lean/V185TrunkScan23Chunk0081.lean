import V185TrunkScan23Chunk0080

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_481294 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_481294 : Nat := 118140960795 + 481294 * 2 ^ 59
def prefixEnd_481294 : Nat := 4983230072969 + 3 ^ 40 * 481294 * 2
def baseEnd_481294 : Nat := 247135158125145168711575

theorem tailTrace_481294 : CollatzResearch.WordTrace tailWord_481294 prefixEnd_481294 247135158125145168711575 := by
  unfold tailWord_481294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2194279289795188914519367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11702822878907674210769957 2194279289795188914519367)
  ·
    refine ⟨3291418934692783371779051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2194279289795188914519367 3291418934692783371779051)
    ·
      refine ⟨4937128402039175057668577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3291418934692783371779051 4937128402039175057668577)
      ·
        refine ⟨3702846301529381293251433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4937128402039175057668577 3702846301529381293251433)
        ·
          refine ⟨2777134726147035969938575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3702846301529381293251433 2777134726147035969938575)
          ·
            refine ⟨4165702089220553954907863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777134726147035969938575 4165702089220553954907863)
            ·
              refine ⟨6248553133830830932361795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4165702089220553954907863 6248553133830830932361795)
              ·
                refine ⟨9372829700746246398542693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6248553133830830932361795 9372829700746246398542693)
                ·
                  refine ⟨1757405568889921199726755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9372829700746246398542693 1757405568889921199726755)
                  ·
                    refine ⟨2636108353334881799590133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1757405568889921199726755 2636108353334881799590133)
                    ·
                      refine ⟨247135158125145168711575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2636108353334881799590133 247135158125145168711575)
                      ·
                        rfl

theorem cell23_481294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_481294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481294 prefixEnd_481294 := by exact prefixLift 481294
  have htrace : WordTrace (prefixWord ++ tailWord_481294) baseStart_481294 baseEnd_481294 := by
    simpa [prefixWord, tailWord_481294, baseEnd_481294] using wordTrace_append hprefix tailTrace_481294
  have hstable : (prefixWord ++ tailWord_481294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481294).length < 2 ^ (prefixWord ++ tailWord_481294).sum := by decide
  have hdescent : baseEnd_481294 < baseStart_481294 := by decide
  rcases family_descends (prefixWord ++ tailWord_481294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481307 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 7]
def baseStart_481307 : Nat := 118140960795 + 481307 * 2 ^ 59
def prefixEnd_481307 : Nat := 4983230072969 + 3 ^ 40 * 481307 * 2
def baseEnd_481307 : Nat := 247141833373653617849015

theorem tailTrace_481307 : CollatzResearch.WordTrace tailWord_481307 prefixEnd_481307 247141833373653617849015 := by
  unfold tailWord_481307
  simp only [CollatzResearch.WordTrace]
  refine ⟨17554708467314414536378175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11703138978209609690918783 17554708467314414536378175)
  ·
    refine ⟨26332062700971621804567263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17554708467314414536378175 26332062700971621804567263)
    ·
      refine ⟨39498094051457432706850895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26332062700971621804567263 39498094051457432706850895)
      ·
        refine ⟨59247141077186149060276343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39498094051457432706850895 59247141077186149060276343)
        ·
          refine ⟨88870711615779223590414515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59247141077186149060276343 88870711615779223590414515)
          ·
            refine ⟨133306067423668835385621773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88870711615779223590414515 133306067423668835385621773)
            ·
              refine ⟨49989775283875813269608165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133306067423668835385621773 49989775283875813269608165)
              ·
                refine ⟨9373082865726714988051531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49989775283875813269608165 9373082865726714988051531)
                ·
                  refine ⟨14059624298590072482077297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9373082865726714988051531 14059624298590072482077297)
                  ·
                    refine ⟨10544718223942554361557973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14059624298590072482077297 10544718223942554361557973)
                    ·
                      refine ⟨247141833373653617849015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10544718223942554361557973 247141833373653617849015)
                      ·
                        rfl

theorem cell23_481307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_481307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481307 prefixEnd_481307 := by exact prefixLift 481307
  have htrace : WordTrace (prefixWord ++ tailWord_481307) baseStart_481307 baseEnd_481307 := by
    simpa [prefixWord, tailWord_481307, baseEnd_481307] using wordTrace_append hprefix tailTrace_481307
  have hstable : (prefixWord ++ tailWord_481307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481307).length < 2 ^ (prefixWord ++ tailWord_481307).sum := by decide
  have hdescent : baseEnd_481307 < baseStart_481307 := by decide
  rcases family_descends (prefixWord ++ tailWord_481307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481308 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_481308 : Nat := 118140960795 + 481308 * 2 ^ 59
def prefixEnd_481308 : Nat := 4983230072969 + 3 ^ 40 * 481308 * 2
def baseEnd_481308 : Nat := 247142346854308113936511

theorem tailTrace_481308 : CollatzResearch.WordTrace tailWord_481308 prefixEnd_481308 247142346854308113936511 := by
  unfold tailWord_481308
  simp only [CollatzResearch.WordTrace]
  refine ⟨8777372470155395853582289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11703163293540527804776385 8777372470155395853582289)
  ·
    refine ⟨6583029352616546890186717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8777372470155395853582289 6583029352616546890186717)
    ·
      refine ⟨2468636007231205083820019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6583029352616546890186717 2468636007231205083820019)
      ·
        refine ⟨3702954010846807625730029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2468636007231205083820019 3702954010846807625730029)
        ·
          refine ⟨1388607754067552859648761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3702954010846807625730029 1388607754067552859648761)
          ·
            refine ⟨1041455815550664644736571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1388607754067552859648761 1041455815550664644736571)
            ·
              refine ⟨1562183723325996967104857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041455815550664644736571 1562183723325996967104857)
              ·
                refine ⟨1171637792494497725328643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1562183723325996967104857 1171637792494497725328643)
                ·
                  refine ⟨1757456688741746587992965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171637792494497725328643 1757456688741746587992965)
                  ·
                    refine ⟨329523129139077485248681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1757456688741746587992965 329523129139077485248681)
                    ·
                      refine ⟨247142346854308113936511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 329523129139077485248681 247142346854308113936511)
                      ·
                        rfl

theorem cell23_481308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_481308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481308 prefixEnd_481308 := by exact prefixLift 481308
  have htrace : WordTrace (prefixWord ++ tailWord_481308) baseStart_481308 baseEnd_481308 := by
    simpa [prefixWord, tailWord_481308, baseEnd_481308] using wordTrace_append hprefix tailTrace_481308
  have hstable : (prefixWord ++ tailWord_481308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481308).length < 2 ^ (prefixWord ++ tailWord_481308).sum := by decide
  have hdescent : baseEnd_481308 < baseStart_481308 := by decide
  rcases family_descends (prefixWord ++ tailWord_481308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481341 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_481341 : Nat := 118140960795 + 481341 * 2 ^ 59
def prefixEnd_481341 : Nat := 4983230072969 + 3 ^ 40 * 481341 * 2
def baseEnd_481341 : Nat := 247159291715906484823859

theorem tailTrace_481341 : CollatzResearch.WordTrace tailWord_481341 prefixEnd_481341 247159291715906484823859 := by
  unfold tailWord_481341
  simp only [CollatzResearch.WordTrace]
  refine ⟨17555948549191238343115877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11703965699460825562077251 17555948549191238343115877)
  ·
    refine ⟨3291740352973357189334227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17555948549191238343115877 3291740352973357189334227)
    ·
      refine ⟨4937610529460035784001341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3291740352973357189334227 4937610529460035784001341)
      ·
        refine ⟨1851603948547513419000503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4937610529460035784001341 1851603948547513419000503)
        ·
          refine ⟨2777405922821270128500755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851603948547513419000503 2777405922821270128500755)
          ·
            refine ⟨4166108884231905192751133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777405922821270128500755 4166108884231905192751133)
            ·
              refine ⟨1562290831586964447281675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4166108884231905192751133 1562290831586964447281675)
              ·
                refine ⟨2343436247380446670922513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562290831586964447281675 2343436247380446670922513)
                ·
                  refine ⟨1757577185535335003191885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2343436247380446670922513 1757577185535335003191885)
                  ·
                    refine ⟨659091444575750626196957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1757577185535335003191885 659091444575750626196957)
                    ·
                      refine ⟨247159291715906484823859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 659091444575750626196957 247159291715906484823859)
                      ·
                        rfl

theorem cell23_481341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_481341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481341 prefixEnd_481341 := by exact prefixLift 481341
  have htrace : WordTrace (prefixWord ++ tailWord_481341) baseStart_481341 baseEnd_481341 := by
    simpa [prefixWord, tailWord_481341, baseEnd_481341] using wordTrace_append hprefix tailTrace_481341
  have hstable : (prefixWord ++ tailWord_481341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481341).length < 2 ^ (prefixWord ++ tailWord_481341).sum := by decide
  have hdescent : baseEnd_481341 < baseStart_481341 := by decide
  rcases family_descends (prefixWord ++ tailWord_481341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481351 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 2, 5, 2]
def baseStart_481351 : Nat := 118140960795 + 481351 * 2 ^ 59
def prefixEnd_481351 : Nat := 4983230072969 + 3 ^ 40 * 481351 * 2
def baseEnd_481351 : Nat := 247164426522451445698813

theorem tailTrace_481351 : CollatzResearch.WordTrace tailWord_481351 prefixEnd_481351 247164426522451445698813 := by
  unfold tailWord_481351
  simp only [CollatzResearch.WordTrace]
  refine ⟨17556313279155010050979907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11704208852770006700653271 17556313279155010050979907)
  ·
    refine ⟨26334469918732515076469861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17556313279155010050979907 26334469918732515076469861)
    ·
      refine ⟨4937713109762346576838099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26334469918732515076469861 4937713109762346576838099)
      ·
        refine ⟨7406569664643519865257149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4937713109762346576838099 7406569664643519865257149)
        ·
          refine ⟨2777463624241319949471431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7406569664643519865257149 2777463624241319949471431)
          ·
            refine ⟨4166195436361979924207147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777463624241319949471431 4166195436361979924207147)
            ·
              refine ⟨6249293154542969886310721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4166195436361979924207147 6249293154542969886310721)
              ·
                refine ⟨4686969865907227414733041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6249293154542969886310721 4686969865907227414733041)
                ·
                  refine ⟨3515227399430420561049781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4686969865907227414733041 3515227399430420561049781)
                  ·
                    refine ⟨329552568696601927598417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3515227399430420561049781 329552568696601927598417)
                    ·
                      refine ⟨247164426522451445698813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 329552568696601927598417 247164426522451445698813)
                      ·
                        rfl

theorem cell23_481351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_481351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481351 prefixEnd_481351 := by exact prefixLift 481351
  have htrace : WordTrace (prefixWord ++ tailWord_481351) baseStart_481351 baseEnd_481351 := by
    simpa [prefixWord, tailWord_481351, baseEnd_481351] using wordTrace_append hprefix tailTrace_481351
  have hstable : (prefixWord ++ tailWord_481351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481351).length < 2 ^ (prefixWord ++ tailWord_481351).sum := by decide
  have hdescent : baseEnd_481351 < baseStart_481351 := by decide
  rcases family_descends (prefixWord ++ tailWord_481351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481391 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 3, 4]
def baseStart_481391 : Nat := 118140960795 + 481391 * 2 ^ 59
def prefixEnd_481391 : Nat := 4983230072969 + 3 ^ 40 * 481391 * 2
def baseEnd_481391 : Nat := 82394988582877096399543

theorem tailTrace_481391 : CollatzResearch.WordTrace tailWord_481391 prefixEnd_481391 82394988582877096399543 := by
  unfold tailWord_481391
  simp only [CollatzResearch.WordTrace]
  refine ⟨17557772199010096882436027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11705181466006731254957351 17557772199010096882436027)
  ·
    refine ⟨26336658298515145323654041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17557772199010096882436027 26336658298515145323654041)
    ·
      refine ⟨19752493723886358992740531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26336658298515145323654041 19752493723886358992740531)
      ·
        refine ⟨29628740585829538489110797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19752493723886358992740531 29628740585829538489110797)
        ·
          refine ⟨11110777719686076933416549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29628740585829538489110797 11110777719686076933416549)
          ·
            refine ⟨2083270822441139425015603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11110777719686076933416549 2083270822441139425015603)
            ·
              refine ⟨3124906233661709137523405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083270822441139425015603 3124906233661709137523405)
              ·
                refine ⟨1171839837623140926571277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3124906233661709137523405 1171839837623140926571277)
                ·
                  refine ⟨439439939108677847464229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171839837623140926571277 439439939108677847464229)
                  ·
                    refine ⟨82394988582877096399543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 439439939108677847464229 82394988582877096399543)
                    ·
                      rfl

theorem cell23_481391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 4].length) (baseStart_481391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481391 prefixEnd_481391 := by exact prefixLift 481391
  have htrace : WordTrace (prefixWord ++ tailWord_481391) baseStart_481391 baseEnd_481391 := by
    simpa [prefixWord, tailWord_481391, baseEnd_481391] using wordTrace_append hprefix tailTrace_481391
  have hstable : (prefixWord ++ tailWord_481391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481391).length < 2 ^ (prefixWord ++ tailWord_481391).sum := by decide
  have hdescent : baseEnd_481391 < baseStart_481391 := by decide
  rcases family_descends (prefixWord ++ tailWord_481391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481401 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 1, 4, 3]
def baseStart_481401 : Nat := 118140960795 + 481401 * 2 ^ 59
def prefixEnd_481401 : Nat := 4983230072969 + 3 ^ 40 * 481401 * 2
def baseEnd_481401 : Nat := 247190100555176250073583

theorem tailTrace_481401 : CollatzResearch.WordTrace tailWord_481401 prefixEnd_481401 247190100555176250073583 := by
  unfold tailWord_481401
  simp only [CollatzResearch.WordTrace]
  refine ⟨17558136928973868590300057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11705424619315912393533371 17558136928973868590300057)
  ·
    refine ⟨13168602696730401442725043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17558136928973868590300057 13168602696730401442725043)
    ·
      refine ⟨19752904045095602164087565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13168602696730401442725043 19752904045095602164087565)
      ·
        refine ⟨7407339016910850811532837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19752904045095602164087565 7407339016910850811532837)
        ·
          refine ⟨1388876065670784527162407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7407339016910850811532837 1388876065670784527162407)
          ·
            refine ⟨2083314098506176790743611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388876065670784527162407 2083314098506176790743611)
            ·
              refine ⟨3124971147759265186115417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083314098506176790743611 3124971147759265186115417)
              ·
                refine ⟨2343728360819448889586563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3124971147759265186115417 2343728360819448889586563)
                ·
                  refine ⟨3515592541229173334379845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343728360819448889586563 3515592541229173334379845)
                  ·
                    refine ⟨659173601480470000196221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3515592541229173334379845 659173601480470000196221)
                    ·
                      refine ⟨247190100555176250073583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 659173601480470000196221 247190100555176250073583)
                      ·
                        rfl

theorem cell23_481401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_481401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481401 prefixEnd_481401 := by exact prefixLift 481401
  have htrace : WordTrace (prefixWord ++ tailWord_481401) baseStart_481401 baseEnd_481401 := by
    simpa [prefixWord, tailWord_481401, baseEnd_481401] using wordTrace_append hprefix tailTrace_481401
  have hstable : (prefixWord ++ tailWord_481401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481401).length < 2 ^ (prefixWord ++ tailWord_481401).sum := by decide
  have hdescent : baseEnd_481401 < baseStart_481401 := by decide
  rcases family_descends (prefixWord ++ tailWord_481401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481458 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2]
def baseStart_481458 : Nat := 118140960795 + 481458 * 2 ^ 59
def prefixEnd_481458 : Nat := 4983230072969 + 3 ^ 40 * 481458 * 2
def baseEnd_481458 : Nat := 247219368952482527060821

theorem tailTrace_481458 : CollatzResearch.WordTrace tailWord_481458 prefixEnd_481458 247219368952482527060821 := by
  unfold tailWord_481458
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390053972441841831281257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11706810593178244883416685 4390053972441841831281257)
  ·
    refine ⟨3292540479331381373460943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4390053972441841831281257 3292540479331381373460943)
    ·
      refine ⟨4938810718997072060191415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3292540479331381373460943 4938810718997072060191415)
      ·
        refine ⟨7408216078495608090287123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4938810718997072060191415 7408216078495608090287123)
        ·
          refine ⟨11112324117743412135430685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7408216078495608090287123 11112324117743412135430685)
          ·
            refine ⟨4167121544153779550786507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11112324117743412135430685 4167121544153779550786507)
            ·
              refine ⟨6250682316230669326179761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4167121544153779550786507 6250682316230669326179761)
              ·
                refine ⟨4688011737173001994634821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6250682316230669326179761 4688011737173001994634821)
                ·
                  refine ⟨879002200719937873994029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4688011737173001994634821 879002200719937873994029)
                  ·
                    refine ⟨329625825269976702747761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 879002200719937873994029 329625825269976702747761)
                    ·
                      refine ⟨247219368952482527060821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 329625825269976702747761 247219368952482527060821)
                      ·
                        rfl

theorem cell23_481458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_481458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481458 prefixEnd_481458 := by exact prefixLift 481458
  have htrace : WordTrace (prefixWord ++ tailWord_481458) baseStart_481458 baseEnd_481458 := by
    simpa [prefixWord, tailWord_481458, baseEnd_481458] using wordTrace_append hprefix tailTrace_481458
  have hstable : (prefixWord ++ tailWord_481458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481458).length < 2 ^ (prefixWord ++ tailWord_481458).sum := by decide
  have hdescent : baseEnd_481458 < baseStart_481458 := by decide
  rcases family_descends (prefixWord ++ tailWord_481458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481468 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 3, 5]
def baseStart_481468 : Nat := 118140960795 + 481468 * 2 ^ 59
def prefixEnd_481468 : Nat := 4983230072969 + 3 ^ 40 * 481468 * 2
def baseEnd_481468 : Nat := 82408167919675829311925

theorem tailTrace_481468 : CollatzResearch.WordTrace tailWord_481468 prefixEnd_481468 82408167919675829311925 := by
  unfold tailWord_481468
  simp only [CollatzResearch.WordTrace]
  refine ⟨8780290309865569516494529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11707053746487426021992705 8780290309865569516494529)
  ·
    refine ⟨6585217732399177137370897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8780290309865569516494529 6585217732399177137370897)
    ·
      refine ⟨4938913299299382853028173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6585217732399177137370897 4938913299299382853028173)
      ·
        refine ⟨1852092487237268569885565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4938913299299382853028173 1852092487237268569885565)
        ·
          refine ⟨694534682713975713707087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1852092487237268569885565 694534682713975713707087)
          ·
            refine ⟨1041802024070963570560631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694534682713975713707087 1041802024070963570560631)
            ·
              refine ⟨1562703036106445355840947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041802024070963570560631 1562703036106445355840947)
              ·
                refine ⟨2344054554159668033761421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562703036106445355840947 2344054554159668033761421)
                ·
                  refine ⟨879020457809875512660533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2344054554159668033761421 879020457809875512660533)
                  ·
                    refine ⟨82408167919675829311925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 879020457809875512660533 82408167919675829311925)
                    ·
                      rfl

theorem cell23_481468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_481468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481468 prefixEnd_481468 := by exact prefixLift 481468
  have htrace : WordTrace (prefixWord ++ tailWord_481468) baseStart_481468 baseEnd_481468 := by
    simpa [prefixWord, tailWord_481468, baseEnd_481468] using wordTrace_append hprefix tailTrace_481468
  have hstable : (prefixWord ++ tailWord_481468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481468).length < 2 ^ (prefixWord ++ tailWord_481468).sum := by decide
  have hdescent : baseEnd_481468 < baseStart_481468 := by decide
  rcases family_descends (prefixWord ++ tailWord_481468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481481 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 4, 4]
def baseStart_481481 : Nat := 118140960795 + 481481 * 2 ^ 59
def prefixEnd_481481 : Nat := 4983230072969 + 3 ^ 40 * 481481 * 2
def baseEnd_481481 : Nat := 82410393002511979024405

theorem tailTrace_481481 : CollatzResearch.WordTrace tailWord_481481 prefixEnd_481481 82410393002511979024405 := by
  unfold tailWord_481481
  simp only [CollatzResearch.WordTrace]
  refine ⟨17561054768684042253212297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11707369845789361502141531 17561054768684042253212297)
  ·
    refine ⟨13170791076513031689909223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17561054768684042253212297 13170791076513031689909223)
    ·
      refine ⟨19756186614769547534863835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13170791076513031689909223 19756186614769547534863835)
      ·
        refine ⟨29634279922154321302295753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19756186614769547534863835 29634279922154321302295753)
        ·
          refine ⟨22225709941615740976721815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29634279922154321302295753 22225709941615740976721815)
          ·
            refine ⟨33338564912423611465082723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22225709941615740976721815 33338564912423611465082723)
            ·
              refine ⟨50007847368635417197624085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33338564912423611465082723 50007847368635417197624085)
              ·
                refine ⟨2344117845404785181138629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50007847368635417197624085 2344117845404785181138629)
                ·
                  refine ⟨439522096013397221463493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2344117845404785181138629 439522096013397221463493)
                  ·
                    refine ⟨82410393002511979024405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 439522096013397221463493 82410393002511979024405)
                    ·
                      rfl

theorem cell23_481481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 4].length) (baseStart_481481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481481 prefixEnd_481481 := by exact prefixLift 481481
  have htrace : WordTrace (prefixWord ++ tailWord_481481) baseStart_481481 baseEnd_481481 := by
    simpa [prefixWord, tailWord_481481, baseEnd_481481] using wordTrace_append hprefix tailTrace_481481
  have hstable : (prefixWord ++ tailWord_481481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481481).length < 2 ^ (prefixWord ++ tailWord_481481).sum := by decide
  have hdescent : baseEnd_481481 < baseStart_481481 := by decide
  rcases family_descends (prefixWord ++ tailWord_481481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481491 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 3]
def baseStart_481491 : Nat := 118140960795 + 481491 * 2 ^ 59
def prefixEnd_481491 : Nat := 4983230072969 + 3 ^ 40 * 481491 * 2
def baseEnd_481491 : Nat := 247236313814080897948169

theorem tailTrace_481491 : CollatzResearch.WordTrace tailWord_481491 prefixEnd_481491 247236313814080897948169 := by
  unfold tailWord_481491
  simp only [CollatzResearch.WordTrace]
  refine ⟨17561419498647813961076327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11707612999098542640717551 17561419498647813961076327)
  ·
    refine ⟨26342129247971720941614491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17561419498647813961076327 26342129247971720941614491)
    ·
      refine ⟨39513193871957581412421737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26342129247971720941614491 39513193871957581412421737)
      ·
        refine ⟨29634895403968186059316303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39513193871957581412421737 29634895403968186059316303)
        ·
          refine ⟨44452343105952279088974455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29634895403968186059316303 44452343105952279088974455)
          ·
            refine ⟨66678514658928418633461683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44452343105952279088974455 66678514658928418633461683)
            ·
              refine ⟨100017771988392627950192525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66678514658928418633461683 100017771988392627950192525)
              ·
                refine ⟨37506664495647235481322197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100017771988392627950192525 37506664495647235481322197)
                ·
                  refine ⟨879062449116732081593489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 37506664495647235481322197 879062449116732081593489)
                  ·
                    refine ⟨659296836837549061195117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 879062449116732081593489 659296836837549061195117)
                    ·
                      refine ⟨247236313814080897948169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 659296836837549061195117 247236313814080897948169)
                      ·
                        rfl

theorem cell23_481491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 3].length) (baseStart_481491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481491 prefixEnd_481491 := by exact prefixLift 481491
  have htrace : WordTrace (prefixWord ++ tailWord_481491) baseStart_481491 baseEnd_481491 := by
    simpa [prefixWord, tailWord_481491, baseEnd_481491] using wordTrace_append hprefix tailTrace_481491
  have hstable : (prefixWord ++ tailWord_481491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481491).length < 2 ^ (prefixWord ++ tailWord_481491).sum := by decide
  have hdescent : baseEnd_481491 < baseStart_481491 := by decide
  rcases family_descends (prefixWord ++ tailWord_481491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481498 : List Nat := [3, 1, 1, 2, 2, 1, 3, 4, 2, 4]
def baseStart_481498 : Nat := 118140960795 + 481498 * 2 ^ 59
def prefixEnd_481498 : Nat := 4983230072969 + 3 ^ 40 * 481498 * 2
def baseEnd_481498 : Nat := 82413302726220790186879

theorem tailTrace_481498 : CollatzResearch.WordTrace tailWord_481498 prefixEnd_481498 82413302726220790186879 := by
  unfold tailWord_481498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390418702405613539145287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11707783206414969437720765 4390418702405613539145287)
  ·
    refine ⟨6585628053608420308717931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4390418702405613539145287 6585628053608420308717931)
    ·
      refine ⟨9878442080412630463076897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6585628053608420308717931 9878442080412630463076897)
      ·
        refine ⟨7408831560309472847307673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9878442080412630463076897 7408831560309472847307673)
        ·
          refine ⟨5556623670232104635480755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7408831560309472847307673 5556623670232104635480755)
          ·
            refine ⟨8334935505348156953221133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556623670232104635480755 8334935505348156953221133)
            ·
              refine ⟨3125600814505558857457925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8334935505348156953221133 3125600814505558857457925)
              ·
                refine ⟨586050152719792285773361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3125600814505558857457925 586050152719792285773361)
                ·
                  refine ⟨439537614539844214330021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586050152719792285773361 439537614539844214330021)
                  ·
                    refine ⟨82413302726220790186879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 439537614539844214330021 82413302726220790186879)
                    ·
                      rfl

theorem cell23_481498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_481498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481498 prefixEnd_481498 := by exact prefixLift 481498
  have htrace : WordTrace (prefixWord ++ tailWord_481498) baseStart_481498 baseEnd_481498 := by
    simpa [prefixWord, tailWord_481498, baseEnd_481498] using wordTrace_append hprefix tailTrace_481498
  have hstable : (prefixWord ++ tailWord_481498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481498).length < 2 ^ (prefixWord ++ tailWord_481498).sum := by decide
  have hdescent : baseEnd_481498 < baseStart_481498 := by decide
  rcases family_descends (prefixWord ++ tailWord_481498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481505 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 3, 2, 2]
def baseStart_481505 : Nat := 118140960795 + 481505 * 2 ^ 59
def prefixEnd_481505 : Nat := 4983230072969 + 3 ^ 40 * 481505 * 2
def baseEnd_481505 : Nat := 247243502543243843173105

theorem tailTrace_481505 : CollatzResearch.WordTrace tailWord_481505 prefixEnd_481505 247243502543243843173105 := by
  unfold tailWord_481505
  simp only [CollatzResearch.WordTrace]
  refine ⟨17561930120597094352085969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11707953413731396234723979 17561930120597094352085969)
  ·
    refine ⟨13171447590447820764064477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17561930120597094352085969 13171447590447820764064477)
    ·
      refine ⟨4939292846417932786524179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13171447590447820764064477 4939292846417932786524179)
      ·
        refine ⟨7408939269626899179786269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4939292846417932786524179 7408939269626899179786269)
        ·
          refine ⟨2778352226110087192419851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7408939269626899179786269 2778352226110087192419851)
          ·
            refine ⟨4167528339165130788629777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778352226110087192419851 4167528339165130788629777)
            ·
              refine ⟨3125646254373848091472333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4167528339165130788629777 3125646254373848091472333)
              ·
                refine ⟨1172117345390193034302125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3125646254373848091472333 1172117345390193034302125)
                ·
                  refine ⟨439544004521322387863297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172117345390193034302125 439544004521322387863297)
                  ·
                    refine ⟨329658003390991790897473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 439544004521322387863297 329658003390991790897473)
                    ·
                      refine ⟨247243502543243843173105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 329658003390991790897473 247243502543243843173105)
                      ·
                        rfl

theorem cell23_481505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_481505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481505 prefixEnd_481505 := by exact prefixLift 481505
  have htrace : WordTrace (prefixWord ++ tailWord_481505) baseStart_481505 baseEnd_481505 := by
    simpa [prefixWord, tailWord_481505, baseEnd_481505] using wordTrace_append hprefix tailTrace_481505
  have hstable : (prefixWord ++ tailWord_481505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481505).length < 2 ^ (prefixWord ++ tailWord_481505).sum := by decide
  have hdescent : baseEnd_481505 < baseStart_481505 := by decide
  rcases family_descends (prefixWord ++ tailWord_481505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481522 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 3, 2, 2]
def baseStart_481522 : Nat := 118140960795 + 481522 * 2 ^ 59
def prefixEnd_481522 : Nat := 4983230072969 + 3 ^ 40 * 481522 * 2
def baseEnd_481522 : Nat := 247252231714370276660527

theorem tailTrace_481522 : CollatzResearch.WordTrace tailWord_481522 prefixEnd_481522 247252231714370276660527 := by
  unfold tailWord_481522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390637540383876563863705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11708366774357004170303213 4390637540383876563863705)
  ·
    refine ⟨3292978155287907422897779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4390637540383876563863705 3292978155287907422897779)
    ·
      refine ⟨4939467232931861134346669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3292978155287907422897779 4939467232931861134346669)
      ·
        refine ⟨1852300212349447925380001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4939467232931861134346669 1852300212349447925380001)
        ·
          refine ⟨1389225159262085944035001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1852300212349447925380001 1389225159262085944035001)
          ·
            refine ⟨1041918869446564458026251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1389225159262085944035001 1041918869446564458026251)
            ·
              refine ⟨1562878304169846687039377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041918869446564458026251 1562878304169846687039377)
              ·
                refine ⟨1172158728127385015279533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1562878304169846687039377 1172158728127385015279533)
                ·
                  refine ⟨439559523047769380729825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172158728127385015279533 439559523047769380729825)
                  ·
                    refine ⟨329669642285827035547369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 439559523047769380729825 329669642285827035547369)
                    ·
                      refine ⟨247252231714370276660527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 329669642285827035547369 247252231714370276660527)
                      ·
                        rfl

theorem cell23_481522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_481522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481522 prefixEnd_481522 := by exact prefixLift 481522
  have htrace : WordTrace (prefixWord ++ tailWord_481522) baseStart_481522 baseEnd_481522 := by
    simpa [prefixWord, tailWord_481522, baseEnd_481522] using wordTrace_append hprefix tailTrace_481522
  have hstable : (prefixWord ++ tailWord_481522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481522).length < 2 ^ (prefixWord ++ tailWord_481522).sum := by decide
  have hdescent : baseEnd_481522 < baseStart_481522 := by decide
  rcases family_descends (prefixWord ++ tailWord_481522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481571 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 2, 6]
def baseStart_481571 : Nat := 118140960795 + 481571 * 2 ^ 59
def prefixEnd_481571 : Nat := 4983230072969 + 3 ^ 40 * 481571 * 2
def baseEnd_481571 : Nat := 82425797422146861649267

theorem tailTrace_481571 : CollatzResearch.WordTrace tailWord_481571 prefixEnd_481571 82425797422146861649267 := by
  unfold tailWord_481571
  simp only [CollatzResearch.WordTrace]
  refine ⟨17564337338357987623988567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11709558225571991749325711 17564337338357987623988567)
  ·
    refine ⟨26346506007536981435982851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17564337338357987623988567 26346506007536981435982851)
    ·
      refine ⟨39519759011305472153974277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26346506007536981435982851 39519759011305472153974277)
      ·
        refine ⟨7409954814619776028870177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39519759011305472153974277 7409954814619776028870177)
        ·
          refine ⟨5557466110964832021652633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7409954814619776028870177 5557466110964832021652633)
          ·
            refine ⟨4168099583223624016239475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5557466110964832021652633 4168099583223624016239475)
            ·
              refine ⟨6252149374835436024359213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4168099583223624016239475 6252149374835436024359213)
              ·
                refine ⟨2344556015563288509134705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6252149374835436024359213 2344556015563288509134705)
                ·
                  refine ⟨1758417011672466381851029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2344556015563288509134705 1758417011672466381851029)
                  ·
                    refine ⟨82425797422146861649267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1758417011672466381851029 82425797422146861649267)
                    ·
                      rfl

theorem cell23_481571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 6].length) (baseStart_481571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481571 prefixEnd_481571 := by exact prefixLift 481571
  have htrace : WordTrace (prefixWord ++ tailWord_481571) baseStart_481571 baseEnd_481571 := by
    simpa [prefixWord, tailWord_481571, baseEnd_481571] using wordTrace_append hprefix tailTrace_481571
  have hstable : (prefixWord ++ tailWord_481571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481571).length < 2 ^ (prefixWord ++ tailWord_481571).sum := by decide
  have hdescent : baseEnd_481571 < baseStart_481571 := by decide
  rcases family_descends (prefixWord ++ tailWord_481571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481591 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_481591 : Nat := 118140960795 + 481591 * 2 ^ 59
def prefixEnd_481591 : Nat := 4983230072969 + 3 ^ 40 * 481591 * 2
def baseEnd_481591 : Nat := 247287661879530506697709

theorem tailTrace_481591 : CollatzResearch.WordTrace tailWord_481591 prefixEnd_481591 247287661879530506697709 := by
  unfold tailWord_481591
  simp only [CollatzResearch.WordTrace]
  refine ⟨17565066798285531039716627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11710044532190354026477751 17565066798285531039716627)
  ·
    refine ⟨26347600197428296559574941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17565066798285531039716627 26347600197428296559574941)
    ·
      refine ⟨9880350074035611209840603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26347600197428296559574941 9880350074035611209840603)
      ·
        refine ⟨14820525111053416814760905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9880350074035611209840603 14820525111053416814760905)
        ·
          refine ⟨11115393833290062611070679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14820525111053416814760905 11115393833290062611070679)
          ·
            refine ⟨16673090749935093916606019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11115393833290062611070679 16673090749935093916606019)
            ·
              refine ⟨25009636124902640874909029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16673090749935093916606019 25009636124902640874909029)
              ·
                refine ⟨4689306773419245164045443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25009636124902640874909029 4689306773419245164045443)
                ·
                  refine ⟨7033960160128867746068165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689306773419245164045443 7033960160128867746068165)
                  ·
                    refine ⟨1318867530024162702387781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7033960160128867746068165 1318867530024162702387781)
                    ·
                      refine ⟨247287661879530506697709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1318867530024162702387781 247287661879530506697709)
                      ·
                        rfl

theorem cell23_481591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_481591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481591 prefixEnd_481591 := by exact prefixLift 481591
  have htrace : WordTrace (prefixWord ++ tailWord_481591) baseStart_481591 baseEnd_481591 := by
    simpa [prefixWord, tailWord_481591, baseEnd_481591] using wordTrace_append hprefix tailTrace_481591
  have hstable : (prefixWord ++ tailWord_481591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481591).length < 2 ^ (prefixWord ++ tailWord_481591).sum := by decide
  have hdescent : baseEnd_481591 < baseStart_481591 := by decide
  rcases family_descends (prefixWord ++ tailWord_481591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481598 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_481598 : Nat := 118140960795 + 481598 * 2 ^ 59
def prefixEnd_481598 : Nat := 4983230072969 + 3 ^ 40 * 481598 * 2
def baseEnd_481598 : Nat := 247291256244111979310177

theorem tailTrace_481598 : CollatzResearch.WordTrace tailWord_481598 prefixEnd_481598 247291256244111979310177 := by
  unfold tailWord_481598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2195665263657521404402681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11710214739506780823480965 2195665263657521404402681)
  ·
    refine ⟨1646748947743141053302011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2195665263657521404402681 1646748947743141053302011)
    ·
      refine ⟨2470123421614711579953017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1646748947743141053302011 2470123421614711579953017)
      ·
        refine ⟨1852592566211033684964763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2470123421614711579953017 1852592566211033684964763)
        ·
          refine ⟨2778888849316550527447145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852592566211033684964763 2778888849316550527447145)
          ·
            refine ⟨2084166636987412895585359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2778888849316550527447145 2084166636987412895585359)
            ·
              refine ⟨3126249955481119343378039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084166636987412895585359 3126249955481119343378039)
              ·
                refine ⟨4689374933221679015067059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126249955481119343378039 4689374933221679015067059)
                ·
                  refine ⟨7034062399832518522600589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689374933221679015067059 7034062399832518522600589)
                  ·
                    refine ⟨2637773399937194445975221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7034062399832518522600589 2637773399937194445975221)
                    ·
                      refine ⟨247291256244111979310177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2637773399937194445975221 247291256244111979310177)
                      ·
                        rfl

theorem cell23_481598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_481598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481598 prefixEnd_481598 := by exact prefixLift 481598
  have htrace : WordTrace (prefixWord ++ tailWord_481598) baseStart_481598 baseEnd_481598 := by
    simpa [prefixWord, tailWord_481598, baseEnd_481598] using wordTrace_append hprefix tailTrace_481598
  have hstable : (prefixWord ++ tailWord_481598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481598).length < 2 ^ (prefixWord ++ tailWord_481598).sum := by decide
  have hdescent : baseEnd_481598 < baseStart_481598 := by decide
  rcases family_descends (prefixWord ++ tailWord_481598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481612 : List Nat := [2, 2, 1, 3, 2, 1, 2, 4, 2, 2, 2]
def baseStart_481612 : Nat := 118140960795 + 481612 * 2 ^ 59
def prefixEnd_481612 : Nat := 4983230072969 + 3 ^ 40 * 481612 * 2
def baseEnd_481612 : Nat := 247298444973274924535113

theorem tailTrace_481612 : CollatzResearch.WordTrace tailWord_481612 prefixEnd_481612 247298444973274924535113 := by
  unfold tailWord_481612
  simp only [CollatzResearch.WordTrace]
  refine ⟨8782916365604725813115545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11710555154139634417487393 8782916365604725813115545)
  ·
    refine ⟨6587187274203544359836659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8782916365604725813115545 6587187274203544359836659)
    ·
      refine ⟨9880780911305316539754989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6587187274203544359836659 9880780911305316539754989)
      ·
        refine ⟨3705292841739493702408121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9880780911305316539754989 3705292841739493702408121)
        ·
          refine ⟨2778969631304620276806091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3705292841739493702408121 2778969631304620276806091)
          ·
            refine ⟨4168454446956930415209137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778969631304620276806091 4168454446956930415209137)
            ·
              refine ⟨3126340835217697811406853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4168454446956930415209137 3126340835217697811406853)
              ·
                refine ⟨586188906603318339638785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3126340835217697811406853 586188906603318339638785)
                ·
                  refine ⟨439641679952488754729089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586188906603318339638785 439641679952488754729089)
                  ·
                    refine ⟨329731259964366566046817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 439641679952488754729089 329731259964366566046817)
                    ·
                      refine ⟨247298444973274924535113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 329731259964366566046817 247298444973274924535113)
                      ·
                        rfl

theorem cell23_481612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_481612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481612 prefixEnd_481612 := by exact prefixLift 481612
  have htrace : WordTrace (prefixWord ++ tailWord_481612) baseStart_481612 baseEnd_481612 := by
    simpa [prefixWord, tailWord_481612, baseEnd_481612] using wordTrace_append hprefix tailTrace_481612
  have hstable : (prefixWord ++ tailWord_481612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481612).length < 2 ^ (prefixWord ++ tailWord_481612).sum := by decide
  have hdescent : baseEnd_481612 < baseStart_481612 := by decide
  rcases family_descends (prefixWord ++ tailWord_481612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481618 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 7]
def baseStart_481618 : Nat := 118140960795 + 481618 * 2 ^ 59
def prefixEnd_481618 : Nat := 4983230072969 + 3 ^ 40 * 481618 * 2
def baseEnd_481618 : Nat := 27477947317466877895565

theorem tailTrace_481618 : CollatzResearch.WordTrace tailWord_481618 prefixEnd_481618 27477947317466877895565 := by
  unfold tailWord_481618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4391512892296928662737377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11710701046125143100633005 4391512892296928662737377)
  ·
    refine ⟨3293634669222696497053033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4391512892296928662737377 3293634669222696497053033)
    ·
      refine ⟨2470226001917022372789775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3293634669222696497053033 2470226001917022372789775)
      ·
        refine ⟨3705339002875533559184663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470226001917022372789775 3705339002875533559184663)
        ·
          refine ⟨5558008504313300338776995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3705339002875533559184663 5558008504313300338776995)
          ·
            refine ⟨8337012756469950508165493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5558008504313300338776995 8337012756469950508165493)
            ·
              refine ⟨781594945919057860140515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8337012756469950508165493 781594945919057860140515)
              ·
                refine ⟨1172392418878586790210773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781594945919057860140515 1172392418878586790210773)
                ·
                  refine ⟨27477947317466877895565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1172392418878586790210773 27477947317466877895565)
                  ·
                    rfl

theorem cell23_481618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_481618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481618 prefixEnd_481618 := by exact prefixLift 481618
  have htrace : WordTrace (prefixWord ++ tailWord_481618) baseStart_481618 baseEnd_481618 := by
    simpa [prefixWord, tailWord_481618, baseEnd_481618] using wordTrace_append hprefix tailTrace_481618
  have hstable : (prefixWord ++ tailWord_481618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481618).length < 2 ^ (prefixWord ++ tailWord_481618).sum := by decide
  have hdescent : baseEnd_481618 < baseStart_481618 := by decide
  rcases family_descends (prefixWord ++ tailWord_481618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481631 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 3, 7]
def baseStart_481631 : Nat := 118140960795 + 481631 * 2 ^ 59
def prefixEnd_481631 : Nat := 4983230072969 + 3 ^ 40 * 481631 * 2
def baseEnd_481631 : Nat := 82436067035236783399175

theorem tailTrace_481631 : CollatzResearch.WordTrace tailWord_481631 prefixEnd_481631 82436067035236783399175 := by
  unfold tailWord_481631
  simp only [CollatzResearch.WordTrace]
  refine ⟨17566525718140617871172747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11711017145427078580781831 17566525718140617871172747)
  ·
    refine ⟨26349788577210926806759121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17566525718140617871172747 26349788577210926806759121)
    ·
      refine ⟨19762341432908195105069341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26349788577210926806759121 19762341432908195105069341)
      ·
        refine ⟨7410878037340573164401003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19762341432908195105069341 7410878037340573164401003)
        ·
          refine ⟨11116317056010859746601505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7410878037340573164401003 11116317056010859746601505)
          ·
            refine ⟨8337237792008144809951129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11116317056010859746601505 8337237792008144809951129)
            ·
              refine ⟨6252928344006108607463347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8337237792008144809951129 6252928344006108607463347)
              ·
                refine ⟨9379392516009162911195021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6252928344006108607463347 9379392516009162911195021)
                ·
                  refine ⟨3517272193503436091698133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9379392516009162911195021 3517272193503436091698133)
                  ·
                    refine ⟨82436067035236783399175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3517272193503436091698133 82436067035236783399175)
                    ·
                      rfl

theorem cell23_481631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_481631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481631 prefixEnd_481631 := by exact prefixLift 481631
  have htrace : WordTrace (prefixWord ++ tailWord_481631) baseStart_481631 baseEnd_481631 := by
    simpa [prefixWord, tailWord_481631, baseEnd_481631] using wordTrace_append hprefix tailTrace_481631
  have hstable : (prefixWord ++ tailWord_481631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481631).length < 2 ^ (prefixWord ++ tailWord_481631).sum := by decide
  have hdescent : baseEnd_481631 < baseStart_481631 := by decide
  rcases family_descends (prefixWord ++ tailWord_481631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481641 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 7]
def baseStart_481641 : Nat := 118140960795 + 481641 * 2 ^ 59
def prefixEnd_481641 : Nat := 4983230072969 + 3 ^ 40 * 481641 * 2
def baseEnd_481641 : Nat := 247313335912255311072479

theorem tailTrace_481641 : CollatzResearch.WordTrace tailWord_481641 prefixEnd_481641 247313335912255311072479 := by
  unfold tailWord_481641
  simp only [CollatzResearch.WordTrace]
  refine ⟨17566890448104389579036777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11711260298736259719357851 17566890448104389579036777)
  ·
    refine ⟨13175167836078292184277583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17566890448104389579036777 13175167836078292184277583)
    ·
      refine ⟨19762751754117438276416375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13175167836078292184277583 19762751754117438276416375)
      ·
        refine ⟨29644127631176157414624563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19762751754117438276416375 29644127631176157414624563)
        ·
          refine ⟨44466191446764236121936845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29644127631176157414624563 44466191446764236121936845)
          ·
            refine ⟨16674821792536588545726317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44466191446764236121936845 16674821792536588545726317)
            ·
              refine ⟨6253058172201220704647369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16674821792536588545726317 6253058172201220704647369)
              ·
                refine ⟨4689793629150915528485527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6253058172201220704647369 4689793629150915528485527)
                ·
                  refine ⟨7034690443726373292728291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689793629150915528485527 7034690443726373292728291)
                  ·
                    refine ⟨10552035665589559939092437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7034690443726373292728291 10552035665589559939092437)
                    ·
                      refine ⟨247313335912255311072479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10552035665589559939092437 247313335912255311072479)
                      ·
                        rfl

theorem cell23_481641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_481641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481641 prefixEnd_481641 := by exact prefixLift 481641
  have htrace : WordTrace (prefixWord ++ tailWord_481641) baseStart_481641 baseEnd_481641 := by
    simpa [prefixWord, tailWord_481641, baseEnd_481641] using wordTrace_append hprefix tailTrace_481641
  have hstable : (prefixWord ++ tailWord_481641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481641).length < 2 ^ (prefixWord ++ tailWord_481641).sum := by decide
  have hdescent : baseEnd_481641 < baseStart_481641 := by decide
  rcases family_descends (prefixWord ++ tailWord_481641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481648 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 2, 5]
def baseStart_481648 : Nat := 118140960795 + 481648 * 2 ^ 59
def prefixEnd_481648 : Nat := 4983230072969 + 3 ^ 40 * 481648 * 2
def baseEnd_481648 : Nat := 82438976758945594561649

theorem tailTrace_481648 : CollatzResearch.WordTrace tailWord_481648 prefixEnd_481648 82438976758945594561649 := by
  unfold tailWord_481648
  simp only [CollatzResearch.WordTrace]
  refine ⟨8783572879539514887270799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11711430506052686516361065 8783572879539514887270799)
  ·
    refine ⟨13175359319309272330906199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8783572879539514887270799 13175359319309272330906199)
    ·
      refine ⟨19763038978963908496359299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13175359319309272330906199 19763038978963908496359299)
      ·
        refine ⟨29644558468445862744538949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19763038978963908496359299 29644558468445862744538949)
        ·
          refine ⟨5558354712833599264601053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29644558468445862744538949 5558354712833599264601053)
          ·
            refine ⟨2084383017312599724225395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5558354712833599264601053 2084383017312599724225395)
            ·
              refine ⟨3126574525968899586338093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084383017312599724225395 3126574525968899586338093)
              ·
                refine ⟨1172465447238337344876785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3126574525968899586338093 1172465447238337344876785)
                ·
                  refine ⟨879349085428753008657589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1172465447238337344876785 879349085428753008657589)
                  ·
                    refine ⟨82438976758945594561649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 879349085428753008657589 82438976758945594561649)
                    ·
                      rfl

theorem cell23_481648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 2, 5].length) (baseStart_481648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481648 prefixEnd_481648 := by exact prefixLift 481648
  have htrace : WordTrace (prefixWord ++ tailWord_481648) baseStart_481648 baseEnd_481648 := by
    simpa [prefixWord, tailWord_481648, baseEnd_481648] using wordTrace_append hprefix tailTrace_481648
  have hstable : (prefixWord ++ tailWord_481648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481648).length < 2 ^ (prefixWord ++ tailWord_481648).sum := by decide
  have hdescent : baseEnd_481648 < baseStart_481648 := by decide
  rcases family_descends (prefixWord ++ tailWord_481648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481665 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 2, 5]
def baseStart_481665 : Nat := 118140960795 + 481665 * 2 ^ 59
def prefixEnd_481665 : Nat := 4983230072969 + 3 ^ 40 * 481665 * 2
def baseEnd_481665 : Nat := 82441886482654405724123

theorem tailTrace_481665 : CollatzResearch.WordTrace tailWord_481665 prefixEnd_481665 82441886482654405724123 := by
  unfold tailWord_481665
  simp only [CollatzResearch.WordTrace]
  refine ⟨17567765800017441677910449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11711843866678294451940299 17567765800017441677910449)
  ·
    refine ⟨13175824350013081258432837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17567765800017441677910449 13175824350013081258432837)
    ·
      refine ⟨2470467065627452735956157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13175824350013081258432837 2470467065627452735956157)
      ·
        refine ⟨926425149610294775983559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2470467065627452735956157 926425149610294775983559)
        ·
          refine ⟨1389637724415442163975339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926425149610294775983559 1389637724415442163975339)
          ·
            refine ⟨2084456586623163245963009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389637724415442163975339 2084456586623163245963009)
            ·
              refine ⟨1563342439967372434472257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2084456586623163245963009 1563342439967372434472257)
              ·
                refine ⟨1172506829975529325854193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1563342439967372434472257 1172506829975529325854193)
                ·
                  refine ⟨879380122481646994390645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1172506829975529325854193 879380122481646994390645)
                  ·
                    refine ⟨82441886482654405724123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 879380122481646994390645 82441886482654405724123)
                    ·
                      rfl

theorem cell23_481665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_481665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481665 prefixEnd_481665 := by exact prefixLift 481665
  have htrace : WordTrace (prefixWord ++ tailWord_481665) baseStart_481665 baseEnd_481665 := by
    simpa [prefixWord, tailWord_481665, baseEnd_481665] using wordTrace_append hprefix tailTrace_481665
  have hstable : (prefixWord ++ tailWord_481665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481665).length < 2 ^ (prefixWord ++ tailWord_481665).sum := by decide
  have hdescent : baseEnd_481665 < baseStart_481665 := by decide
  rcases family_descends (prefixWord ++ tailWord_481665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481695 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 3, 4]
def baseStart_481695 : Nat := 118140960795 + 481695 * 2 ^ 59
def prefixEnd_481695 : Nat := 4983230072969 + 3 ^ 40 * 481695 * 2
def baseEnd_481695 : Nat := 82447021289199366599077

theorem tailTrace_481695 : CollatzResearch.WordTrace tailWord_481695 prefixEnd_481695 82447021289199366599077 := by
  unfold tailWord_481695
  simp only [CollatzResearch.WordTrace]
  refine ⟨17568859989908756801502539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11712573326605837867668359 17568859989908756801502539)
  ·
    refine ⟨26353289984863135202253809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17568859989908756801502539 26353289984863135202253809)
    ·
      refine ⟨19764967488647351401690357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26353289984863135202253809 19764967488647351401690357)
      ·
        refine ⟨1852965702060689193908471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19764967488647351401690357 1852965702060689193908471)
        ·
          refine ⟨2779448553091033790862707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852965702060689193908471 2779448553091033790862707)
          ·
            refine ⟨4169172829636550686294061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779448553091033790862707 4169172829636550686294061)
            ·
              refine ⟨1563439811113706507360273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4169172829636550686294061 1563439811113706507360273)
              ·
                refine ⟨1172579858335279880520205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1563439811113706507360273 1172579858335279880520205)
                ·
                  refine ⟨439717446875729955195077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172579858335279880520205 439717446875729955195077)
                  ·
                    refine ⟨82447021289199366599077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 439717446875729955195077 82447021289199366599077)
                    ·
                      rfl

theorem cell23_481695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 4].length) (baseStart_481695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481695 prefixEnd_481695 := by exact prefixLift 481695
  have htrace : WordTrace (prefixWord ++ tailWord_481695) baseStart_481695 baseEnd_481695 := by
    simpa [prefixWord, tailWord_481695, baseEnd_481695] using wordTrace_append hprefix tailTrace_481695
  have hstable : (prefixWord ++ tailWord_481695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481695).length < 2 ^ (prefixWord ++ tailWord_481695).sum := by decide
  have hdescent : baseEnd_481695 < baseStart_481695 := by decide
  rcases family_descends (prefixWord ++ tailWord_481695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481725 : List Nat := [1, 4, 1, 2, 2, 2, 3, 2, 6]
def baseStart_481725 : Nat := 118140960795 + 481725 * 2 ^ 59
def prefixEnd_481725 : Nat := 4983230072969 + 3 ^ 40 * 481725 * 2
def baseEnd_481725 : Nat := 27484052031914775824677

theorem tailTrace_481725 : CollatzResearch.WordTrace tailWord_481725 prefixEnd_481725 27484052031914775824677 := by
  unfold tailWord_481725
  simp only [CollatzResearch.WordTrace]
  refine ⟨17569954179800071925094629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11713302786533381283396419 17569954179800071925094629)
  ·
    refine ⟨3294366408712513485955243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17569954179800071925094629 3294366408712513485955243)
    ·
      refine ⟨4941549613068770228932865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3294366408712513485955243 4941549613068770228932865)
      ·
        refine ⟨3706162209801577671699649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4941549613068770228932865 3706162209801577671699649)
        ·
          refine ⟨2779621657351183253774737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3706162209801577671699649 2779621657351183253774737)
          ·
            refine ⟨2084716243013387440331053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2779621657351183253774737 2084716243013387440331053)
            ·
              refine ⟨781768591130020290124145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2084716243013387440331053 781768591130020290124145)
              ·
                refine ⟨586326443347515217593109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781768591130020290124145 586326443347515217593109)
                ·
                  refine ⟨27484052031914775824677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 586326443347515217593109 27484052031914775824677)
                  ·
                    rfl

theorem cell23_481725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_481725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481725 prefixEnd_481725 := by exact prefixLift 481725
  have htrace : WordTrace (prefixWord ++ tailWord_481725) baseStart_481725 baseEnd_481725 := by
    simpa [prefixWord, tailWord_481725, baseEnd_481725] using wordTrace_append hprefix tailTrace_481725
  have hstable : (prefixWord ++ tailWord_481725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481725).length < 2 ^ (prefixWord ++ tailWord_481725).sum := by decide
  have hdescent : baseEnd_481725 < baseStart_481725 := by decide
  rcases family_descends (prefixWord ++ tailWord_481725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481785 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 4, 4]
def baseStart_481785 : Nat := 118140960795 + 481785 * 2 ^ 59
def prefixEnd_481785 : Nat := 4983230072969 + 3 ^ 40 * 481785 * 2
def baseEnd_481785 : Nat := 82462425708834249223939

theorem tailTrace_481785 : CollatzResearch.WordTrace tailWord_481785 prefixEnd_481785 82462425708834249223939 := by
  unfold tailWord_481785
  simp only [CollatzResearch.WordTrace]
  refine ⟨17572142559582702172278809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11714761706388468114852539 17572142559582702172278809)
  ·
    refine ⟨13179106919687026629209107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17572142559582702172278809 13179106919687026629209107)
    ·
      refine ⟨19768660379530539943813661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13179106919687026629209107 19768660379530539943813661)
      ·
        refine ⟨7413247642323952478930123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19768660379530539943813661 7413247642323952478930123)
        ·
          refine ⟨11119871463485928718395185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7413247642323952478930123 11119871463485928718395185)
          ·
            refine ⟨8339903597614446538796389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11119871463485928718395185 8339903597614446538796389)
            ·
              refine ⟨1563731924552708726024323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8339903597614446538796389 1563731924552708726024323)
              ·
                refine ⟨2345597886829063089036485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1563731924552708726024323 2345597886829063089036485)
                ·
                  refine ⟨439799603780449329194341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2345597886829063089036485 439799603780449329194341)
                  ·
                    refine ⟨82462425708834249223939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 439799603780449329194341 82462425708834249223939)
                    ·
                      rfl

theorem cell23_481785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 4].length) (baseStart_481785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481785 prefixEnd_481785 := by exact prefixLift 481785
  have htrace : WordTrace (prefixWord ++ tailWord_481785) baseStart_481785 baseEnd_481785 := by
    simpa [prefixWord, tailWord_481785, baseEnd_481785] using wordTrace_append hprefix tailTrace_481785
  have hstable : (prefixWord ++ tailWord_481785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481785).length < 2 ^ (prefixWord ++ tailWord_481785).sum := by decide
  have hdescent : baseEnd_481785 < baseStart_481785 := by decide
  rcases family_descends (prefixWord ++ tailWord_481785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481795 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 3]
def baseStart_481795 : Nat := 118140960795 + 481795 * 2 ^ 59
def prefixEnd_481795 : Nat := 4983230072969 + 3 ^ 40 * 481795 * 2
def baseEnd_481795 : Nat := 247392411933047708546771

theorem tailTrace_481795 : CollatzResearch.WordTrace tailWord_481795 prefixEnd_481795 247392411933047708546771 := by
  unfold tailWord_481795
  simp only [CollatzResearch.WordTrace]
  refine ⟨17572507289546473880142839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11715004859697649253428559 17572507289546473880142839)
  ·
    refine ⟨26358760934319710820214259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17572507289546473880142839 26358760934319710820214259)
    ·
      refine ⟨39538141401479566230321389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26358760934319710820214259 39538141401479566230321389)
      ·
        refine ⟨14826803025554837336370521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39538141401479566230321389 14826803025554837336370521)
        ·
          refine ⟨11120102269166128002277891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14826803025554837336370521 11120102269166128002277891)
          ·
            refine ⟨16680153403749192003416837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11120102269166128002277891 16680153403749192003416837)
            ·
              refine ⟨3127528763202973500640657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16680153403749192003416837 3127528763202973500640657)
              ·
                refine ⟨2345646572402230125480493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127528763202973500640657 2345646572402230125480493)
                ·
                  refine ⟨879617464650836297055185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2345646572402230125480493 879617464650836297055185)
                  ·
                    refine ⟨659713098488127222791389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 879617464650836297055185 659713098488127222791389)
                    ·
                      refine ⟨247392411933047708546771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 659713098488127222791389 247392411933047708546771)
                      ·
                        rfl

theorem cell23_481795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_481795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481795 prefixEnd_481795 := by exact prefixLift 481795
  have htrace : WordTrace (prefixWord ++ tailWord_481795) baseStart_481795 baseEnd_481795 := by
    simpa [prefixWord, tailWord_481795, baseEnd_481795] using wordTrace_append hprefix tailTrace_481795
  have hstable : (prefixWord ++ tailWord_481795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481795).length < 2 ^ (prefixWord ++ tailWord_481795).sum := by decide
  have hdescent : baseEnd_481795 < baseStart_481795 := by decide
  rcases family_descends (prefixWord ++ tailWord_481795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481802 : List Nat := [3, 1, 2, 2, 2, 1, 3, 3, 2, 4]
def baseStart_481802 : Nat := 118140960795 + 481802 * 2 ^ 59
def prefixEnd_481802 : Nat := 4983230072969 + 3 ^ 40 * 481802 * 2
def baseEnd_481802 : Nat := 82465335432543060386413

theorem tailTrace_481802 : CollatzResearch.WordTrace tailWord_481802 prefixEnd_481802 82465335432543060386413 := by
  unfold tailWord_481802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4393190650130278518911915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11715175067014076050431773 4393190650130278518911915)
  ·
    refine ⟨6589785975195417778367873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4393190650130278518911915 6589785975195417778367873)
    ·
      refine ⟨4942339481396563333775905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6589785975195417778367873 4942339481396563333775905)
      ·
        refine ⟨3706754611047422500331929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4942339481396563333775905 3706754611047422500331929)
        ·
          refine ⟨2780065958285566875248947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3706754611047422500331929 2780065958285566875248947)
          ·
            refine ⟨4170098937428350312873421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2780065958285566875248947 4170098937428350312873421)
            ·
              refine ⟨1563787101535631367327533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4170098937428350312873421 1563787101535631367327533)
              ·
                refine ⟨586420163075861762747825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1563787101535631367327533 586420163075861762747825)
                ·
                  refine ⟨439815122306896322060869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586420163075861762747825 439815122306896322060869)
                  ·
                    refine ⟨82465335432543060386413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 439815122306896322060869 82465335432543060386413)
                    ·
                      rfl

theorem cell23_481802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_481802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481802 prefixEnd_481802 := by exact prefixLift 481802
  have htrace : WordTrace (prefixWord ++ tailWord_481802) baseStart_481802 baseEnd_481802 := by
    simpa [prefixWord, tailWord_481802, baseEnd_481802] using wordTrace_append hprefix tailTrace_481802
  have hstable : (prefixWord ++ tailWord_481802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481802).length < 2 ^ (prefixWord ++ tailWord_481802).sum := by decide
  have hdescent : baseEnd_481802 < baseStart_481802 := by decide
  rcases family_descends (prefixWord ++ tailWord_481802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481826 : List Nat := [3, 3, 1, 1, 1, 1, 1, 7, 1, 2, 2]
def baseStart_481826 : Nat := 118140960795 + 481826 * 2 ^ 59
def prefixEnd_481826 : Nat := 4983230072969 + 3 ^ 40 * 481826 * 2
def baseEnd_481826 : Nat := 247408329833337087259129

theorem tailTrace_481826 : CollatzResearch.WordTrace tailWord_481826 prefixEnd_481826 247408329833337087259129 := by
  unfold tailWord_481826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4393409488108541543630333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11715758634956110783014221 4393409488108541543630333)
  ·
    refine ⟨1647528558040703078861375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4393409488108541543630333 1647528558040703078861375)
    ·
      refine ⟨2471292837061054618292063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1647528558040703078861375 2471292837061054618292063)
      ·
        refine ⟨3706939255591581927438095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2471292837061054618292063 3706939255591581927438095)
        ·
          refine ⟨5560408883387372891157143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706939255591581927438095 5560408883387372891157143)
          ·
            refine ⟨8340613325081059336735715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5560408883387372891157143 8340613325081059336735715)
            ·
              refine ⟨12510919987621589005103573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8340613325081059336735715 12510919987621589005103573)
              ·
                refine ⟨293224687209880992307115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12510919987621589005103573 293224687209880992307115)
                ·
                  refine ⟨439837030814821488460673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293224687209880992307115 439837030814821488460673)
                  ·
                    refine ⟨329877773111116116345505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 439837030814821488460673 329877773111116116345505)
                    ·
                      refine ⟨247408329833337087259129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 329877773111116116345505 247408329833337087259129)
                      ·
                        rfl

theorem cell23_481826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_481826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481826 prefixEnd_481826 := by exact prefixLift 481826
  have htrace : WordTrace (prefixWord ++ tailWord_481826) baseStart_481826 baseEnd_481826 := by
    simpa [prefixWord, tailWord_481826, baseEnd_481826] using wordTrace_append hprefix tailTrace_481826
  have hstable : (prefixWord ++ tailWord_481826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481826).length < 2 ^ (prefixWord ++ tailWord_481826).sum := by decide
  have hdescent : baseEnd_481826 < baseStart_481826 := by decide
  rcases family_descends (prefixWord ++ tailWord_481826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481842 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3]
def baseStart_481842 : Nat := 118140960795 + 481842 * 2 ^ 59
def prefixEnd_481842 : Nat := 4983230072969 + 3 ^ 40 * 481842 * 2
def baseEnd_481842 : Nat := 247416545523809024659055

theorem tailTrace_481842 : CollatzResearch.WordTrace tailWord_481842 prefixEnd_481842 247416545523809024659055 := by
  unfold tailWord_481842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4393555380094050226775945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11716147680250800604735853 4393555380094050226775945)
  ·
    refine ⟨3295166535070537670081959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4393555380094050226775945 3295166535070537670081959)
    ·
      refine ⟨4942749802605806505122939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3295166535070537670081959 4942749802605806505122939)
      ·
        refine ⟨7414124703908709757684409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4942749802605806505122939 7414124703908709757684409)
        ·
          refine ⟨5560593527931532318263307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7414124703908709757684409 5560593527931532318263307)
          ·
            refine ⟨8340890291897298477394961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5560593527931532318263307 8340890291897298477394961)
            ·
              refine ⟨6255667718922973858046221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8340890291897298477394961 6255667718922973858046221)
              ·
                refine ⟨2345875394596115196767333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6255667718922973858046221 2345875394596115196767333)
                ·
                  refine ⟨439851636486771599393875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2345875394596115196767333 439851636486771599393875)
                  ·
                    refine ⟨659777454730157399090813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 439851636486771599393875 659777454730157399090813)
                    ·
                      refine ⟨247416545523809024659055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 659777454730157399090813 247416545523809024659055)
                      ·
                        rfl

theorem cell23_481842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_481842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481842 prefixEnd_481842 := by exact prefixLift 481842
  have htrace : WordTrace (prefixWord ++ tailWord_481842) baseStart_481842 baseEnd_481842 := by
    simpa [prefixWord, tailWord_481842, baseEnd_481842] using wordTrace_append hprefix tailTrace_481842
  have hstable : (prefixWord ++ tailWord_481842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481842).length < 2 ^ (prefixWord ++ tailWord_481842).sum := by decide
  have hdescent : baseEnd_481842 < baseStart_481842 := by decide
  rcases family_descends (prefixWord ++ tailWord_481842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481860 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_481860 : Nat := 118140960795 + 481860 * 2 ^ 59
def prefixEnd_481860 : Nat := 4983230072969 + 3 ^ 40 * 481860 * 2
def baseEnd_481860 : Nat := 247425788175589954233973

theorem tailTrace_481860 : CollatzResearch.WordTrace tailWord_481860 prefixEnd_481860 247425788175589954233973 := by
  unfold tailWord_481860
  simp only [CollatzResearch.WordTrace]
  refine ⟨8787439017155494990629517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11716585356207326654172689 8787439017155494990629517)
  ·
    refine ⟨3295289631433310621486069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8787439017155494990629517 3295289631433310621486069)
    ·
      refine ⟨308933402946872870764319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3295289631433310621486069 308933402946872870764319)
      ·
        refine ⟨463400104420309306146479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308933402946872870764319 463400104420309306146479)
        ·
          refine ⟨695100156630463959219719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463400104420309306146479 695100156630463959219719)
          ·
            refine ⟨1042650234945695938829579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695100156630463959219719 1042650234945695938829579)
            ·
              refine ⟨1563975352418543908244369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042650234945695938829579 1563975352418543908244369)
              ·
                refine ⟨1172981514313907931183277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1563975352418543908244369 1172981514313907931183277)
                ·
                  refine ⟨439868067867715474193729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172981514313907931183277 439868067867715474193729)
                  ·
                    refine ⟨329901050900786605645297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 439868067867715474193729 329901050900786605645297)
                    ·
                      refine ⟨247425788175589954233973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 329901050900786605645297 247425788175589954233973)
                      ·
                        rfl

theorem cell23_481860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_481860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481860 prefixEnd_481860 := by exact prefixLift 481860
  have htrace : WordTrace (prefixWord ++ tailWord_481860) baseStart_481860 baseEnd_481860 := by
    simpa [prefixWord, tailWord_481860, baseEnd_481860] using wordTrace_append hprefix tailTrace_481860
  have hstable : (prefixWord ++ tailWord_481860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481860).length < 2 ^ (prefixWord ++ tailWord_481860).sum := by decide
  have hdescent : baseEnd_481860 < baseStart_481860 := by decide
  rcases family_descends (prefixWord ++ tailWord_481860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481893 : List Nat := [1, 3, 1, 3, 5, 1, 1, 2, 2, 1, 3]
def baseStart_481893 : Nat := 118140960795 + 481893 * 2 ^ 59
def prefixEnd_481893 : Nat := 4983230072969 + 3 ^ 40 * 481893 * 2
def baseEnd_481893 : Nat := 247442733037188325121321

theorem tailTrace_481893 : CollatzResearch.WordTrace tailWord_481893 prefixEnd_481893 247442733037188325121321 := by
  unfold tailWord_481893
  simp only [CollatzResearch.WordTrace]
  refine ⟨17576081643191436617210333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11717387762127624411473555 17576081643191436617210333)
  ·
    refine ⟨6591030616196788731453875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17576081643191436617210333 6591030616196788731453875)
    ·
      refine ⟨9886545924295183097180813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6591030616196788731453875 9886545924295183097180813)
      ·
        refine ⟨3707454721610693661442805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9886545924295183097180813 3707454721610693661442805)
        ·
          refine ⟨347573880151002530760263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3707454721610693661442805 347573880151002530760263)
          ·
            refine ⟨521360820226503796140395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347573880151002530760263 521360820226503796140395)
            ·
              refine ⟨782041230339755694210593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521360820226503796140395 782041230339755694210593)
              ·
                refine ⟨586530922754816770657945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782041230339755694210593 586530922754816770657945)
                ·
                  refine ⟨439898192066112577993459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586530922754816770657945 439898192066112577993459)
                  ·
                    refine ⟨659847288099168866990189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 439898192066112577993459 659847288099168866990189)
                    ·
                      refine ⟨247442733037188325121321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 659847288099168866990189 247442733037188325121321)
                      ·
                        rfl

theorem cell23_481893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_481893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481893 prefixEnd_481893 := by exact prefixLift 481893
  have htrace : WordTrace (prefixWord ++ tailWord_481893) baseStart_481893 baseEnd_481893 := by
    simpa [prefixWord, tailWord_481893, baseEnd_481893] using wordTrace_append hprefix tailTrace_481893
  have hstable : (prefixWord ++ tailWord_481893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481893).length < 2 ^ (prefixWord ++ tailWord_481893).sum := by decide
  have hdescent : baseEnd_481893 < baseStart_481893 := by decide
  rcases family_descends (prefixWord ++ tailWord_481893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481899 : List Nat := [1, 1, 1, 1, 2, 2, 1, 8, 2, 2, 2]
def baseStart_481899 : Nat := 118140960795 + 481899 * 2 ^ 59
def prefixEnd_481899 : Nat := 4983230072969 + 3 ^ 40 * 481899 * 2
def baseEnd_481899 : Nat := 247445813921115301646293

theorem tailTrace_481899 : CollatzResearch.WordTrace tailWord_481899 prefixEnd_481899 247445813921115301646293 := by
  unfold tailWord_481899
  simp only [CollatzResearch.WordTrace]
  refine ⟨17576300481169699641928751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11717533654113133094619167 17576300481169699641928751)
  ·
    refine ⟨26364450721754549462893127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17576300481169699641928751 26364450721754549462893127)
    ·
      refine ⟨39546676082631824194339691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26364450721754549462893127 39546676082631824194339691)
      ·
        refine ⟨59320014123947736291509537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39546676082631824194339691 59320014123947736291509537)
        ·
          refine ⟨44490010592960802218632153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59320014123947736291509537 44490010592960802218632153)
          ·
            refine ⟨33367507944720601663974115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44490010592960802218632153 33367507944720601663974115)
            ·
              refine ⟨50051261917080902495961173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33367507944720601663974115 50051261917080902495961173)
              ·
                refine ⟨586538225590791826124545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 50051261917080902495961173 586538225590791826124545)
                ·
                  refine ⟨439903669193093869593409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586538225590791826124545 439903669193093869593409)
                  ·
                    refine ⟨329927751894820402195057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 439903669193093869593409 329927751894820402195057)
                    ·
                      refine ⟨247445813921115301646293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 329927751894820402195057 247445813921115301646293)
                      ·
                        rfl

theorem cell23_481899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 2, 2].length) (baseStart_481899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481899 prefixEnd_481899 := by exact prefixLift 481899
  have htrace : WordTrace (prefixWord ++ tailWord_481899) baseStart_481899 baseEnd_481899 := by
    simpa [prefixWord, tailWord_481899, baseEnd_481899] using wordTrace_append hprefix tailTrace_481899
  have hstable : (prefixWord ++ tailWord_481899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481899).length < 2 ^ (prefixWord ++ tailWord_481899).sum := by decide
  have hdescent : baseEnd_481899 < baseStart_481899 := by decide
  rcases family_descends (prefixWord ++ tailWord_481899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481915 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 3]
def baseStart_481915 : Nat := 118140960795 + 481915 * 2 ^ 59
def prefixEnd_481915 : Nat := 4983230072969 + 3 ^ 40 * 481915 * 2
def baseEnd_481915 : Nat := 247454029611587239046219

theorem tailTrace_481915 : CollatzResearch.WordTrace tailWord_481915 prefixEnd_481915 247454029611587239046219 := by
  unfold tailWord_481915
  simp only [CollatzResearch.WordTrace]
  refine ⟨17576884049111734374511199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11717922699407822916340799 17576884049111734374511199)
  ·
    refine ⟨26365326073667601561766799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17576884049111734374511199 26365326073667601561766799)
    ·
      refine ⟨39547989110501402342650199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26365326073667601561766799 39547989110501402342650199)
      ·
        refine ⟨59321983665752103513975299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39547989110501402342650199 59321983665752103513975299)
        ·
          refine ⟨88982975498628155270962949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59321983665752103513975299 88982975498628155270962949)
          ·
            refine ⟨16684307905992779113305553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88982975498628155270962949 16684307905992779113305553)
            ·
              refine ⟨12513230929494584334979165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16684307905992779113305553 12513230929494584334979165)
              ·
                refine ⟨4692461598560469125617187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12513230929494584334979165 4692461598560469125617187)
                ·
                  refine ⟨7038692397840703688425781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692461598560469125617187 7038692397840703688425781)
                  ·
                    refine ⟨659877412297565970789917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7038692397840703688425781 659877412297565970789917)
                    ·
                      refine ⟨247454029611587239046219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 659877412297565970789917 247454029611587239046219)
                      ·
                        rfl

theorem cell23_481915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 3].length) (baseStart_481915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481915 prefixEnd_481915 := by exact prefixLift 481915
  have htrace : WordTrace (prefixWord ++ tailWord_481915) baseStart_481915 baseEnd_481915 := by
    simpa [prefixWord, tailWord_481915, baseEnd_481915] using wordTrace_append hprefix tailTrace_481915
  have hstable : (prefixWord ++ tailWord_481915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481915).length < 2 ^ (prefixWord ++ tailWord_481915).sum := by decide
  have hdescent : baseEnd_481915 < baseStart_481915 := by decide
  rcases family_descends (prefixWord ++ tailWord_481915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481945 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 1, 2, 5]
def baseStart_481945 : Nat := 118140960795 + 481945 * 2 ^ 59
def prefixEnd_481945 : Nat := 4983230072969 + 3 ^ 40 * 481945 * 2
def baseEnd_481945 : Nat := 247469434031222121671081

theorem tailTrace_481945 : CollatzResearch.WordTrace tailWord_481945 prefixEnd_481945 247469434031222121671081 := by
  unfold tailWord_481945
  simp only [CollatzResearch.WordTrace]
  refine ⟨17577978239003049498103289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11718652159335366332068859 17577978239003049498103289)
  ·
    refine ⟨13183483679252287123577467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17577978239003049498103289 13183483679252287123577467)
    ·
      refine ⟨19775225518878430685366201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13183483679252287123577467 19775225518878430685366201)
      ·
        refine ⟨14831419139158823014024651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19775225518878430685366201 14831419139158823014024651)
        ·
          refine ⟨22247128708738234521036977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14831419139158823014024651 22247128708738234521036977)
          ·
            refine ⟨16685346531553675890777733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22247128708738234521036977 16685346531553675890777733)
            ·
              refine ⟨3128502474666314229520825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16685346531553675890777733 3128502474666314229520825)
              ·
                refine ⟨2346376855999735672140619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3128502474666314229520825 2346376855999735672140619)
                ·
                  refine ⟨3519565283999603508210929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346376855999735672140619 3519565283999603508210929)
                  ·
                    refine ⟨2639673962999702631158197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3519565283999603508210929 2639673962999702631158197)
                    ·
                      refine ⟨247469434031222121671081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2639673962999702631158197 247469434031222121671081)
                      ·
                        rfl

theorem cell23_481945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_481945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481945 prefixEnd_481945 := by exact prefixLift 481945
  have htrace : WordTrace (prefixWord ++ tailWord_481945) baseStart_481945 baseEnd_481945 := by
    simpa [prefixWord, tailWord_481945, baseEnd_481945] using wordTrace_append hprefix tailTrace_481945
  have hstable : (prefixWord ++ tailWord_481945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481945).length < 2 ^ (prefixWord ++ tailWord_481945).sum := by decide
  have hdescent : baseEnd_481945 < baseStart_481945 := by decide
  rcases family_descends (prefixWord ++ tailWord_481945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481955 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 4]
def baseStart_481955 : Nat := 118140960795 + 481955 * 2 ^ 59
def prefixEnd_481955 : Nat := 4983230072969 + 3 ^ 40 * 481955 * 2
def baseEnd_481955 : Nat := 247474568837767082546035

theorem tailTrace_481955 : CollatzResearch.WordTrace tailWord_481955 prefixEnd_481955 247474568837767082546035 := by
  unfold tailWord_481955
  simp only [CollatzResearch.WordTrace]
  refine ⟨17578342968966821205967319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11718895312644547470644879 17578342968966821205967319)
  ·
    refine ⟨26367514453450231808950979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17578342968966821205967319 26367514453450231808950979)
    ·
      refine ⟨39551271680175347713426469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26367514453450231808950979 39551271680175347713426469)
      ·
        refine ⟨7415863440032877696267463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39551271680175347713426469 7415863440032877696267463)
        ·
          refine ⟨11123795160049316544401195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7415863440032877696267463 11123795160049316544401195)
          ·
            refine ⟨16685692740073974816601793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11123795160049316544401195 16685692740073974816601793)
            ·
              refine ⟨12514269555055481112451345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16685692740073974816601793 12514269555055481112451345)
              ·
                refine ⟨9385702166291610834338509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12514269555055481112451345 9385702166291610834338509)
                ·
                  refine ⟨3519638312359354062876941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9385702166291610834338509 3519638312359354062876941)
                  ·
                    refine ⟨1319864367134757773578853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3519638312359354062876941 1319864367134757773578853)
                    ·
                      refine ⟨247474568837767082546035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1319864367134757773578853 247474568837767082546035)
                      ·
                        rfl

theorem cell23_481955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_481955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481955 prefixEnd_481955 := by exact prefixLift 481955
  have htrace : WordTrace (prefixWord ++ tailWord_481955) baseStart_481955 baseEnd_481955 := by
    simpa [prefixWord, tailWord_481955, baseEnd_481955] using wordTrace_append hprefix tailTrace_481955
  have hstable : (prefixWord ++ tailWord_481955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481955).length < 2 ^ (prefixWord ++ tailWord_481955).sum := by decide
  have hdescent : baseEnd_481955 < baseStart_481955 := by decide
  rcases family_descends (prefixWord ++ tailWord_481955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482035 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 7]
def baseStart_482035 : Nat := 118140960795 + 482035 * 2 ^ 59
def prefixEnd_482035 : Nat := 4983230072969 + 3 ^ 40 * 482035 * 2
def baseEnd_482035 : Nat := 247515647290126769545667

theorem tailTrace_482035 : CollatzResearch.WordTrace tailWord_482035 prefixEnd_482035 247515647290126769545667 := by
  unfold tailWord_482035
  simp only [CollatzResearch.WordTrace]
  refine ⟨17581260808676994868879559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11720840539117996579253039 17581260808676994868879559)
  ·
    refine ⟨26371891213015492303319339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17581260808676994868879559 26371891213015492303319339)
    ·
      refine ⟨39557836819523238454979009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26371891213015492303319339 39557836819523238454979009)
      ·
        refine ⟨29668377614642428841234257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39557836819523238454979009 29668377614642428841234257)
        ·
          refine ⟨22251283210981821630925693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29668377614642428841234257 22251283210981821630925693)
          ·
            refine ⟨8344231204118183111597135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22251283210981821630925693 8344231204118183111597135)
            ·
              refine ⟨12516346806177274667395703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8344231204118183111597135 12516346806177274667395703)
              ·
                refine ⟨18774520209265912001093555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12516346806177274667395703 18774520209265912001093555)
                ·
                  refine ⟨28161780313898868001640333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18774520209265912001093555 28161780313898868001640333)
                  ·
                    refine ⟨10560667617712075500615125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28161780313898868001640333 10560667617712075500615125)
                    ·
                      refine ⟨247515647290126769545667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10560667617712075500615125 247515647290126769545667)
                      ·
                        rfl

theorem cell23_482035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_482035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482035 prefixEnd_482035 := by exact prefixLift 482035
  have htrace : WordTrace (prefixWord ++ tailWord_482035) baseStart_482035 baseEnd_482035 := by
    simpa [prefixWord, tailWord_482035, baseEnd_482035] using wordTrace_append hprefix tailTrace_482035
  have hstable : (prefixWord ++ tailWord_482035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482035).length < 2 ^ (prefixWord ++ tailWord_482035).sum := by decide
  have hdescent : baseEnd_482035 < baseStart_482035 := by decide
  rcases family_descends (prefixWord ++ tailWord_482035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482042 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 3, 5]
def baseStart_482042 : Nat := 118140960795 + 482042 * 2 ^ 59
def prefixEnd_482042 : Nat := 4983230072969 + 3 ^ 40 * 482042 * 2
def baseEnd_482042 : Nat := 82506413884902747386045

theorem tailTrace_482042 : CollatzResearch.WordTrace tailWord_482042 prefixEnd_482042 82506413884902747386045 := by
  unfold tailWord_482042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4395379029912908766096095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11721010746434423376256253 4395379029912908766096095)
  ·
    refine ⟨6593068544869363149144143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4395379029912908766096095 6593068544869363149144143)
    ·
      refine ⟨9889602817304044723716215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6593068544869363149144143 9889602817304044723716215)
      ·
        refine ⟨14834404225956067085574323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9889602817304044723716215 14834404225956067085574323)
        ·
          refine ⟨22251606338934100628361485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14834404225956067085574323 22251606338934100628361485)
          ·
            refine ⟨8344352377100287735635557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22251606338934100628361485 8344352377100287735635557)
            ·
              refine ⟨1564566070706303950431667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8344352377100287735635557 1564566070706303950431667)
              ·
                refine ⟨2346849106059455925647501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564566070706303950431667 2346849106059455925647501)
                ·
                  refine ⟨880068414772295972117813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2346849106059455925647501 880068414772295972117813)
                  ·
                    refine ⟨82506413884902747386045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 880068414772295972117813 82506413884902747386045)
                    ·
                      rfl

theorem cell23_482042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_482042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482042 prefixEnd_482042 := by exact prefixLift 482042
  have htrace : WordTrace (prefixWord ++ tailWord_482042) baseStart_482042 baseEnd_482042 := by
    simpa [prefixWord, tailWord_482042, baseEnd_482042] using wordTrace_append hprefix tailTrace_482042
  have hstable : (prefixWord ++ tailWord_482042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482042).length < 2 ^ (prefixWord ++ tailWord_482042).sum := by decide
  have hdescent : baseEnd_482042 < baseStart_482042 := by decide
  rcases family_descends (prefixWord ++ tailWord_482042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482092 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_482092 : Nat := 118140960795 + 482092 * 2 ^ 59
def prefixEnd_482092 : Nat := 4983230072969 + 3 ^ 40 * 482092 * 2
def baseEnd_482092 : Nat := 247544915687433046532905

theorem tailTrace_482092 : CollatzResearch.WordTrace tailWord_482092 prefixEnd_482092 247544915687433046532905 := by
  unfold tailWord_482092
  simp only [CollatzResearch.WordTrace]
  refine ⟨8791669884735246801852265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11722226512980329069136353 8791669884735246801852265)
  ·
    refine ⟨6593752413551435101389199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8791669884735246801852265 6593752413551435101389199)
    ·
      refine ⟨9890628620327152652083799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6593752413551435101389199 9890628620327152652083799)
      ·
        refine ⟨14835942930490728978125699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9890628620327152652083799 14835942930490728978125699)
        ·
          refine ⟨22253914395736093467188549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14835942930490728978125699 22253914395736093467188549)
          ·
            refine ⟨4172608949200517525097853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22253914395736093467188549 4172608949200517525097853)
            ·
              refine ⟨1564728355950194071911695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4172608949200517525097853 1564728355950194071911695)
              ·
                refine ⟨2347092533925291107867543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564728355950194071911695 2347092533925291107867543)
                ·
                  refine ⟨3520638800887936661801315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2347092533925291107867543 3520638800887936661801315)
                  ·
                    refine ⟨5280958201331904992701973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3520638800887936661801315 5280958201331904992701973)
                    ·
                      refine ⟨247544915687433046532905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5280958201331904992701973 247544915687433046532905)
                      ·
                        rfl

theorem cell23_482092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_482092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482092 prefixEnd_482092 := by exact prefixLift 482092
  have htrace : WordTrace (prefixWord ++ tailWord_482092) baseStart_482092 baseEnd_482092 := by
    simpa [prefixWord, tailWord_482092, baseEnd_482092] using wordTrace_append hprefix tailTrace_482092
  have hstable : (prefixWord ++ tailWord_482092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482092).length < 2 ^ (prefixWord ++ tailWord_482092).sum := by decide
  have hdescent : baseEnd_482092 < baseStart_482092 := by decide
  rcases family_descends (prefixWord ++ tailWord_482092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482140 : List Nat := [2, 2, 4, 2, 1, 3, 2, 1, 2, 4]
def baseStart_482140 : Nat := 118140960795 + 482140 * 2 ^ 59
def prefixEnd_482140 : Nat := 4983230072969 + 3 ^ 40 * 482140 * 2
def baseEnd_482140 : Nat := 82523187586282952910895

theorem tailTrace_482140 : CollatzResearch.WordTrace tailWord_482140 prefixEnd_482140 82523187586282952910895 := by
  unfold tailWord_482140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8792545236648298900725937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11723393648864398534301249 8792545236648298900725937)
  ·
    refine ⟨6594408927486224175544453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8792545236648298900725937 6594408927486224175544453)
    ·
      refine ⟨1236451673903667032914585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6594408927486224175544453 1236451673903667032914585)
      ·
        refine ⟨927338755427750274685939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1236451673903667032914585 927338755427750274685939)
        ·
          refine ⟨1391008133141625412028909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927338755427750274685939 1391008133141625412028909)
          ·
            refine ⟨521628049928109529510841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1391008133141625412028909 521628049928109529510841)
            ·
              refine ⟨391221037446082147133131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521628049928109529510841 391221037446082147133131)
              ·
                refine ⟨586831556169123220699697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391221037446082147133131 586831556169123220699697)
                ·
                  refine ⟨440123667126842415524773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586831556169123220699697 440123667126842415524773)
                  ·
                    refine ⟨82523187586282952910895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 440123667126842415524773 82523187586282952910895)
                    ·
                      rfl

theorem cell23_482140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_482140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482140 prefixEnd_482140 := by exact prefixLift 482140
  have htrace : WordTrace (prefixWord ++ tailWord_482140) baseStart_482140 baseEnd_482140 := by
    simpa [prefixWord, tailWord_482140, baseEnd_482140] using wordTrace_append hprefix tailTrace_482140
  have hstable : (prefixWord ++ tailWord_482140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482140).length < 2 ^ (prefixWord ++ tailWord_482140).sum := by decide
  have hdescent : baseEnd_482140 < baseStart_482140 := by decide
  rcases family_descends (prefixWord ++ tailWord_482140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482156 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 3, 3, 2]
def baseStart_482156 : Nat := 118140960795 + 482156 * 2 ^ 59
def prefixEnd_482156 : Nat := 4983230072969 + 3 ^ 40 * 482156 * 2
def baseEnd_482156 : Nat := 247577778449320796132611

theorem tailTrace_482156 : CollatzResearch.WordTrace tailWord_482156 prefixEnd_482156 247577778449320796132611 := by
  unfold tailWord_482156
  simp only [CollatzResearch.WordTrace]
  refine ⟨8792837020619316267017161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11723782694159088356022881 8792837020619316267017161)
  ·
    refine ⟨6594627765464487200262871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8792837020619316267017161 6594627765464487200262871)
    ·
      refine ⟨9891941648196730800394307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6594627765464487200262871 9891941648196730800394307)
      ·
        refine ⟨14837912472295096200591461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9891941648196730800394307 14837912472295096200591461)
        ·
          refine ⟨2782108588555330537610899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14837912472295096200591461 2782108588555330537610899)
          ·
            refine ⟨4173162882832995806416349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2782108588555330537610899 4173162882832995806416349)
            ·
              refine ⟨1564936081062373427406131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4173162882832995806416349 1564936081062373427406131)
              ·
                refine ⟨2347404121593560141109197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564936081062373427406131 2347404121593560141109197)
                ·
                  refine ⟨880276545597585052915949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2347404121593560141109197 880276545597585052915949)
                  ·
                    refine ⟨330103704599094394843481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 880276545597585052915949 330103704599094394843481)
                    ·
                      refine ⟨247577778449320796132611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 330103704599094394843481 247577778449320796132611)
                      ·
                        rfl

theorem cell23_482156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 3, 2].length) (baseStart_482156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482156 prefixEnd_482156 := by exact prefixLift 482156
  have htrace : WordTrace (prefixWord ++ tailWord_482156) baseStart_482156 baseEnd_482156 := by
    simpa [prefixWord, tailWord_482156, baseEnd_482156] using wordTrace_append hprefix tailTrace_482156
  have hstable : (prefixWord ++ tailWord_482156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482156).length < 2 ^ (prefixWord ++ tailWord_482156).sum := by decide
  have hdescent : baseEnd_482156 < baseStart_482156 := by decide
  rcases family_descends (prefixWord ++ tailWord_482156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482199 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_482199 : Nat := 118140960795 + 482199 * 2 ^ 59
def prefixEnd_482199 : Nat := 4983230072969 + 3 ^ 40 * 482199 * 2
def baseEnd_482199 : Nat := 247599858117464127894913

theorem tailTrace_482199 : CollatzResearch.WordTrace tailWord_482199 prefixEnd_482199 247599858117464127894913 := by
  unfold tailWord_482199
  simp only [CollatzResearch.WordTrace]
  refine ⟨17587242380082850877849651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11724828253388567251899767 17587242380082850877849651)
  ·
    refine ⟨26380863570124276316774477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17587242380082850877849651 26380863570124276316774477)
    ·
      refine ⟨9892823838796603618790429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26380863570124276316774477 9892823838796603618790429)
      ·
        refine ⟨3709808939548726357046411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9892823838796603618790429 3709808939548726357046411)
        ·
          refine ⟨5564713409323089535569617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3709808939548726357046411 5564713409323089535569617)
          ·
            refine ⟨4173535056992317151677213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5564713409323089535569617 4173535056992317151677213)
            ·
              refine ⟨1565075646372118931878955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4173535056992317151677213 1565075646372118931878955)
              ·
                refine ⟨2347613469558178397818433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565075646372118931878955 2347613469558178397818433)
                ·
                  refine ⟨1760710102168633798363825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2347613469558178397818433 1760710102168633798363825)
                  ·
                    refine ⟨1320532576626475348772869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1760710102168633798363825 1320532576626475348772869)
                    ·
                      refine ⟨247599858117464127894913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1320532576626475348772869 247599858117464127894913)
                      ·
                        rfl

theorem cell23_482199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_482199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482199 prefixEnd_482199 := by exact prefixLift 482199
  have htrace : WordTrace (prefixWord ++ tailWord_482199) baseStart_482199 baseEnd_482199 := by
    simpa [prefixWord, tailWord_482199, baseEnd_482199] using wordTrace_append hprefix tailTrace_482199
  have hstable : (prefixWord ++ tailWord_482199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482199).length < 2 ^ (prefixWord ++ tailWord_482199).sum := by decide
  have hdescent : baseEnd_482199 < baseStart_482199 := by decide
  rcases family_descends (prefixWord ++ tailWord_482199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482209 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 9]
def baseStart_482209 : Nat := 118140960795 + 482209 * 2 ^ 59
def prefixEnd_482209 : Nat := 4983230072969 + 3 ^ 40 * 482209 * 2
def baseEnd_482209 : Nat := 27511665880445454307763

theorem tailTrace_482209 : CollatzResearch.WordTrace tailWord_482209 prefixEnd_482209 27511665880445454307763 := by
  unfold tailWord_482209
  simp only [CollatzResearch.WordTrace]
  refine ⟨17587607110046622585713681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11725071406697748390475787 17587607110046622585713681)
  ·
    refine ⟨13190705332534966939285261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17587607110046622585713681 13190705332534966939285261)
    ·
      refine ⟨4946514499700612602231973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13190705332534966939285261 4946514499700612602231973)
      ·
        refine ⟨927471468693864862918495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4946514499700612602231973 927471468693864862918495)
        ·
          refine ⟨1391207203040797294377743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927471468693864862918495 1391207203040797294377743)
          ·
            refine ⟨2086810804561195941566615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391207203040797294377743 2086810804561195941566615)
            ·
              refine ⟨3130216206841793912349923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086810804561195941566615 3130216206841793912349923)
              ·
                refine ⟨4695324310262690868524885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3130216206841793912349923 4695324310262690868524885)
                ·
                  refine ⟨27511665880445454307763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4695324310262690868524885 27511665880445454307763)
                  ·
                    rfl

theorem cell23_482209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 9].length) (baseStart_482209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482209 prefixEnd_482209 := by exact prefixLift 482209
  have htrace : WordTrace (prefixWord ++ tailWord_482209) baseStart_482209 baseEnd_482209 := by
    simpa [prefixWord, tailWord_482209, baseEnd_482209] using wordTrace_append hprefix tailTrace_482209
  have hstable : (prefixWord ++ tailWord_482209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482209).length < 2 ^ (prefixWord ++ tailWord_482209).sum := by decide
  have hdescent : baseEnd_482209 < baseStart_482209 := by decide
  rcases family_descends (prefixWord ++ tailWord_482209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482237 : List Nat := [1, 4, 1, 2, 4, 2, 1, 2, 2, 2, 2]
def baseStart_482237 : Nat := 118140960795 + 482237 * 2 ^ 59
def prefixEnd_482237 : Nat := 4983230072969 + 3 ^ 40 * 482237 * 2
def baseEnd_482237 : Nat := 247619370382334979219739

theorem tailTrace_482237 : CollatzResearch.WordTrace tailWord_482237 prefixEnd_482237 247619370382334979219739 := by
  unfold tailWord_482237
  simp only [CollatzResearch.WordTrace]
  refine ⟨17588628353945183367732965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11725752235963455578488643 17588628353945183367732965)
  ·
    refine ⟨3297867816364721881449931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17588628353945183367732965 3297867816364721881449931)
    ·
      refine ⟨4946801724547082822174897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3297867816364721881449931 4946801724547082822174897)
      ·
        refine ⟨3710101293410312116631173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4946801724547082822174897 3710101293410312116631173)
        ·
          refine ⟨695643992514433521868345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3710101293410312116631173 695643992514433521868345)
          ·
            refine ⟨521732994385825141401259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695643992514433521868345 521732994385825141401259)
            ·
              refine ⟨782599491578737712101889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521732994385825141401259 782599491578737712101889)
              ·
                refine ⟨586949618684053284076417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782599491578737712101889 586949618684053284076417)
                ·
                  refine ⟨440212214013039963057313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586949618684053284076417 440212214013039963057313)
                  ·
                    refine ⟨330159160509779972292985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 440212214013039963057313 330159160509779972292985)
                    ·
                      refine ⟨247619370382334979219739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 330159160509779972292985 247619370382334979219739)
                      ·
                        rfl

theorem cell23_482237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_482237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482237 prefixEnd_482237 := by exact prefixLift 482237
  have htrace : WordTrace (prefixWord ++ tailWord_482237) baseStart_482237 baseEnd_482237 := by
    simpa [prefixWord, tailWord_482237, baseEnd_482237] using wordTrace_append hprefix tailTrace_482237
  have hstable : (prefixWord ++ tailWord_482237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482237).length < 2 ^ (prefixWord ++ tailWord_482237).sum := by decide
  have hdescent : baseEnd_482237 < baseStart_482237 := by decide
  rcases family_descends (prefixWord ++ tailWord_482237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482276 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 4, 4, 2]
def baseStart_482276 : Nat := 118140960795 + 482276 * 2 ^ 59
def prefixEnd_482276 : Nat := 4983230072969 + 3 ^ 40 * 482276 * 2
def baseEnd_482276 : Nat := 247639396127860326632059

theorem tailTrace_482276 : CollatzResearch.WordTrace tailWord_482276 prefixEnd_482276 247639396127860326632059 := by
  unfold tailWord_482276
  simp only [CollatzResearch.WordTrace]
  refine ⟨8795025400401946514201341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11726700533869262018935121 8795025400401946514201341)
  ·
    refine ⟨3298134525150729942825503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8795025400401946514201341 3298134525150729942825503)
    ·
      refine ⟨4947201787726094914238255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3298134525150729942825503 4947201787726094914238255)
      ·
        refine ⟨7420802681589142371357383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4947201787726094914238255 7420802681589142371357383)
        ·
          refine ⟨11131204022383713557036075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7420802681589142371357383 11131204022383713557036075)
          ·
            refine ⟨16696806033575570335554113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11131204022383713557036075 16696806033575570335554113)
            ·
              refine ⟨12522604525181677751665585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16696806033575570335554113 12522604525181677751665585)
              ·
                refine ⟨9391953393886258313749189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12522604525181677751665585 9391953393886258313749189)
                ·
                  refine ⟨1760991261353673433827973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9391953393886258313749189 1760991261353673433827973)
                  ·
                    refine ⟨330185861503813768842745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1760991261353673433827973 330185861503813768842745)
                    ·
                      refine ⟨247639396127860326632059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 330185861503813768842745 247639396127860326632059)
                      ·
                        rfl

theorem cell23_482276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_482276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482276 prefixEnd_482276 := by exact prefixLift 482276
  have htrace : WordTrace (prefixWord ++ tailWord_482276) baseStart_482276 baseEnd_482276 := by
    simpa [prefixWord, tailWord_482276, baseEnd_482276] using wordTrace_append hprefix tailTrace_482276
  have hstable : (prefixWord ++ tailWord_482276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482276).length < 2 ^ (prefixWord ++ tailWord_482276).sum := by decide
  have hdescent : baseEnd_482276 < baseStart_482276 := by decide
  rcases family_descends (prefixWord ++ tailWord_482276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482277 : List Nat := [1, 3, 1, 6, 2, 1, 1, 3, 5]
def baseStart_482277 : Nat := 118140960795 + 482277 * 2 ^ 59
def prefixEnd_482277 : Nat := 4983230072969 + 3 ^ 40 * 482277 * 2
def baseEnd_482277 : Nat := 27515545512057202524395

theorem tailTrace_482277 : CollatzResearch.WordTrace tailWord_482277 prefixEnd_482277 27515545512057202524395 := by
  unfold tailWord_482277
  simp only [CollatzResearch.WordTrace]
  refine ⟨17590087273800270199189085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11726724849200180132792723 17590087273800270199189085)
  ·
    refine ⟨6596282727675101324695907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17590087273800270199189085 6596282727675101324695907)
    ·
      refine ⟨9894424091512651987043861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6596282727675101324695907 9894424091512651987043861)
      ·
        refine ⟨463801129289655561892681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9894424091512651987043861 463801129289655561892681)
        ·
          refine ⟨347850846967241671419511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463801129289655561892681 347850846967241671419511)
          ·
            refine ⟨521776270450862507129267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347850846967241671419511 521776270450862507129267)
            ·
              refine ⟨782664405676293760693901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521776270450862507129267 782664405676293760693901)
              ·
                refine ⟨293499152128610160260213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 782664405676293760693901 293499152128610160260213)
                ·
                  refine ⟨27515545512057202524395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 293499152128610160260213 27515545512057202524395)
                  ·
                    rfl

theorem cell23_482277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 5].length) (baseStart_482277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482277 prefixEnd_482277 := by exact prefixLift 482277
  have htrace : WordTrace (prefixWord ++ tailWord_482277) baseStart_482277 baseEnd_482277 := by
    simpa [prefixWord, tailWord_482277, baseEnd_482277] using wordTrace_append hprefix tailTrace_482277
  have hstable : (prefixWord ++ tailWord_482277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482277).length < 2 ^ (prefixWord ++ tailWord_482277).sum := by decide
  have hdescent : baseEnd_482277 < baseStart_482277 := by decide
  rcases family_descends (prefixWord ++ tailWord_482277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482299 : List Nat := [1, 1, 1, 1, 1, 3, 3, 6, 6]
def baseStart_482299 : Nat := 118140960795 + 482299 * 2 ^ 59
def prefixEnd_482299 : Nat := 4983230072969 + 3 ^ 40 * 482299 * 2
def baseEnd_482299 : Nat := 27516800686990415182717

theorem tailTrace_482299 : CollatzResearch.WordTrace tailWord_482299 prefixEnd_482299 27516800686990415182717 := by
  unfold tailWord_482299
  simp only [CollatzResearch.WordTrace]
  refine ⟨17590889679720567956489951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11727259786480378637659967 17590889679720567956489951)
  ·
    refine ⟨26386334519580851934734927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17590889679720567956489951 26386334519580851934734927)
    ·
      refine ⟨39579501779371277902102391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26386334519580851934734927 39579501779371277902102391)
      ·
        refine ⟨59369252669056916853153587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39579501779371277902102391 59369252669056916853153587)
        ·
          refine ⟨89053879003585375279730381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59369252669056916853153587 89053879003585375279730381)
          ·
            refine ⟨33395204626344515729898893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89053879003585375279730381 33395204626344515729898893)
            ·
              refine ⟨12523201734879193398712085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33395204626344515729898893 12523201734879193398712085)
              ·
                refine ⟨587025081322462190564629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12523201734879193398712085 587025081322462190564629)
                ·
                  refine ⟨27516800686990415182717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 587025081322462190564629 27516800686990415182717)
                  ·
                    rfl

theorem cell23_482299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 6].length) (baseStart_482299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482299 prefixEnd_482299 := by exact prefixLift 482299
  have htrace : WordTrace (prefixWord ++ tailWord_482299) baseStart_482299 baseEnd_482299 := by
    simpa [prefixWord, tailWord_482299, baseEnd_482299] using wordTrace_append hprefix tailTrace_482299
  have hstable : (prefixWord ++ tailWord_482299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482299).length < 2 ^ (prefixWord ++ tailWord_482299).sum := by decide
  have hdescent : baseEnd_482299 < baseStart_482299 := by decide
  rcases family_descends (prefixWord ++ tailWord_482299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482316 : List Nat := [2, 2, 1, 2, 3, 3, 1, 3, 6]
def baseStart_482316 : Nat := 118140960795 + 482316 * 2 ^ 59
def prefixEnd_482316 : Nat := 4983230072969 + 3 ^ 40 * 482316 * 2
def baseEnd_482316 : Nat := 27517770594893352236875

theorem tailTrace_482316 : CollatzResearch.WordTrace tailWord_482316 prefixEnd_482316 27517770594893352236875 := by
  unfold tailWord_482316
  simp only [CollatzResearch.WordTrace]
  refine ⟨8795754860329489929929401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11727673147105986573239201 8795754860329489929929401)
  ·
    refine ⟨6596816145247117447447051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8795754860329489929929401 6596816145247117447447051)
    ·
      refine ⟨9895224217870676171170577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6596816145247117447447051 9895224217870676171170577)
      ·
        refine ⟨7421418163403007128377933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9895224217870676171170577 7421418163403007128377933)
        ·
          refine ⟨2783031811276127673141725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7421418163403007128377933 2783031811276127673141725)
          ·
            refine ⟨1043636929228547877428147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2783031811276127673141725 1043636929228547877428147)
            ·
              refine ⟨1565455393842821816142221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043636929228547877428147 1565455393842821816142221)
              ·
                refine ⟨587045772691058181053333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1565455393842821816142221 587045772691058181053333)
                ·
                  refine ⟨27517770594893352236875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 587045772691058181053333 27517770594893352236875)
                  ·
                    rfl

theorem cell23_482316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 6].length) (baseStart_482316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482316 prefixEnd_482316 := by exact prefixLift 482316
  have htrace : WordTrace (prefixWord ++ tailWord_482316) baseStart_482316 baseEnd_482316 := by
    simpa [prefixWord, tailWord_482316, baseEnd_482316] using wordTrace_append hprefix tailTrace_482316
  have hstable : (prefixWord ++ tailWord_482316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482316).length < 2 ^ (prefixWord ++ tailWord_482316).sum := by decide
  have hdescent : baseEnd_482316 < baseStart_482316 := by decide
  rcases family_descends (prefixWord ++ tailWord_482316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482353 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 2, 3, 2]
def baseStart_482353 : Nat := 118140960795 + 482353 * 2 ^ 59
def prefixEnd_482353 : Nat := 4983230072969 + 3 ^ 40 * 482353 * 2
def baseEnd_482353 : Nat := 247678934138256525369205

theorem tailTrace_482353 : CollatzResearch.WordTrace tailWord_482353 prefixEnd_482353 247678934138256525369205 := by
  unfold tailWord_482353
  simp only [CollatzResearch.WordTrace]
  refine ⟨17592859221524935178955713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11728572814349956785970475 17592859221524935178955713)
  ·
    refine ⟨13194644416143701384216785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17592859221524935178955713 13194644416143701384216785)
    ·
      refine ⟨9895983312107776038162589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13194644416143701384216785 9895983312107776038162589)
      ·
        refine ⟨3710993742040416014310971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9895983312107776038162589 3710993742040416014310971)
        ·
          refine ⟨5566490613060624021466457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3710993742040416014310971 5566490613060624021466457)
          ·
            refine ⟨4174867959795468016099843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5566490613060624021466457 4174867959795468016099843)
            ·
              refine ⟨6262301939693202024149765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174867959795468016099843 6262301939693202024149765)
              ·
                refine ⟨1174181613692475379528081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6262301939693202024149765 1174181613692475379528081)
                ·
                  refine ⟨880636210269356534646061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1174181613692475379528081 880636210269356534646061)
                  ·
                    refine ⟨330238578851008700492273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 880636210269356534646061 330238578851008700492273)
                    ·
                      refine ⟨247678934138256525369205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 330238578851008700492273 247678934138256525369205)
                      ·
                        rfl

theorem cell23_482353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_482353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482353 prefixEnd_482353 := by exact prefixLift 482353
  have htrace : WordTrace (prefixWord ++ tailWord_482353) baseStart_482353 baseEnd_482353 := by
    simpa [prefixWord, tailWord_482353, baseEnd_482353] using wordTrace_append hprefix tailTrace_482353
  have hstable : (prefixWord ++ tailWord_482353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482353).length < 2 ^ (prefixWord ++ tailWord_482353).sum := by decide
  have hdescent : baseEnd_482353 < baseStart_482353 := by decide
  rcases family_descends (prefixWord ++ tailWord_482353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482359 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 5, 6]
def baseStart_482359 : Nat := 118140960795 + 482359 * 2 ^ 59
def prefixEnd_482359 : Nat := 4983230072969 + 3 ^ 40 * 482359 * 2
def baseEnd_482359 : Nat := 82560671674061167298059

theorem tailTrace_482359 : CollatzResearch.WordTrace tailWord_482359 prefixEnd_482359 82560671674061167298059 := by
  unfold tailWord_482359
  simp only [CollatzResearch.WordTrace]
  refine ⟨17593078059503198203674131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11728718706335465469116087 17593078059503198203674131)
  ·
    refine ⟨26389617089254797305511197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17593078059503198203674131 26389617089254797305511197)
    ·
      refine ⟨9896106408470548989566699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26389617089254797305511197 9896106408470548989566699)
      ·
        refine ⟨14844159612705823484350049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9896106408470548989566699 14844159612705823484350049)
        ·
          refine ⟨11133119709529367613262537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14844159612705823484350049 11133119709529367613262537)
          ·
            refine ⟨8349839782147025709946903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11133119709529367613262537 8349839782147025709946903)
            ·
              refine ⟨12524759673220538564920355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8349839782147025709946903 12524759673220538564920355)
              ·
                refine ⟨18787139509830807847380533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12524759673220538564920355 18787139509830807847380533)
                ·
                  refine ⟨1761294329046638235691925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18787139509830807847380533 1761294329046638235691925)
                  ·
                    refine ⟨82560671674061167298059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1761294329046638235691925 82560671674061167298059)
                    ·
                      rfl

theorem cell23_482359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_482359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482359 prefixEnd_482359 := by exact prefixLift 482359
  have htrace : WordTrace (prefixWord ++ tailWord_482359) baseStart_482359 baseEnd_482359 := by
    simpa [prefixWord, tailWord_482359, baseEnd_482359] using wordTrace_append hprefix tailTrace_482359
  have hstable : (prefixWord ++ tailWord_482359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482359).length < 2 ^ (prefixWord ++ tailWord_482359).sum := by decide
  have hdescent : baseEnd_482359 < baseStart_482359 := by decide
  rcases family_descends (prefixWord ++ tailWord_482359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482376 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 1, 6]
def baseStart_482376 : Nat := 118140960795 + 482376 * 2 ^ 59
def prefixEnd_482376 : Nat := 4983230072969 + 3 ^ 40 * 482376 * 2
def baseEnd_482376 : Nat := 82563581397769978460533

theorem tailTrace_482376 : CollatzResearch.WordTrace tailWord_482376 prefixEnd_482376 82563581397769978460533 := by
  unfold tailWord_482376
  simp only [CollatzResearch.WordTrace]
  refine ⟨8796849050220805053521491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11729132066961073404695321 8796849050220805053521491)
  ·
    refine ⟨13195273575331207580282237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8796849050220805053521491 13195273575331207580282237)
    ·
      refine ⟨4948227590749202842605839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13195273575331207580282237 4948227590749202842605839)
      ·
        refine ⟨7422341386123804263908759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4948227590749202842605839 7422341386123804263908759)
        ·
          refine ⟨11133512079185706395863139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7422341386123804263908759 11133512079185706395863139)
          ·
            refine ⟨16700268118778559593794709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11133512079185706395863139 16700268118778559593794709)
            ·
              refine ⟨782825068067744980959127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16700268118778559593794709 782825068067744980959127)
              ·
                refine ⟨1174237602101617471438691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782825068067744980959127 1174237602101617471438691)
                ·
                  refine ⟨1761356403152426207158037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174237602101617471438691 1761356403152426207158037)
                  ·
                    refine ⟨82563581397769978460533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1761356403152426207158037 82563581397769978460533)
                    ·
                      rfl

theorem cell23_482376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_482376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482376 prefixEnd_482376 := by exact prefixLift 482376
  have htrace : WordTrace (prefixWord ++ tailWord_482376) baseStart_482376 baseEnd_482376 := by
    simpa [prefixWord, tailWord_482376, baseEnd_482376] using wordTrace_append hprefix tailTrace_482376
  have hstable : (prefixWord ++ tailWord_482376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482376).length < 2 ^ (prefixWord ++ tailWord_482376).sum := by decide
  have hdescent : baseEnd_482376 < baseStart_482376 := by decide
  rcases family_descends (prefixWord ++ tailWord_482376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482410 : List Nat := [3, 1, 3, 2, 2, 1, 3, 2, 2, 4]
def baseStart_482410 : Nat := 118140960795 + 482410 * 2 ^ 59
def prefixEnd_482410 : Nat := 4983230072969 + 3 ^ 40 * 482410 * 2
def baseEnd_482410 : Nat := 82569400845187600785481

theorem tailTrace_482410 : CollatzResearch.WordTrace tailWord_482410 prefixEnd_482410 82569400845187600785481 := by
  unfold tailWord_482410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4398734545579608478445171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11729958788212289275853789 4398734545579608478445171)
  ·
    refine ⟨6598101818369412717667757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4398734545579608478445171 6598101818369412717667757)
    ·
      refine ⟨2474288181888529769125409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6598101818369412717667757 2474288181888529769125409)
      ·
        refine ⟨1855716136416397326844057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2474288181888529769125409 1855716136416397326844057)
        ·
          refine ⟨1391787102312297995133043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1855716136416397326844057 1391787102312297995133043)
          ·
            refine ⟨2087680653468446992699565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391787102312297995133043 2087680653468446992699565)
            ·
              refine ⟨782880245050667622262337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2087680653468446992699565 782880245050667622262337)
              ·
                refine ⟨587160183788000716696753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782880245050667622262337 587160183788000716696753)
                ·
                  refine ⟨440370137841000537522565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587160183788000716696753 440370137841000537522565)
                  ·
                    refine ⟨82569400845187600785481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 440370137841000537522565 82569400845187600785481)
                    ·
                      rfl

theorem cell23_482410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_482410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482410 prefixEnd_482410 := by exact prefixLift 482410
  have htrace : WordTrace (prefixWord ++ tailWord_482410) baseStart_482410 baseEnd_482410 := by
    simpa [prefixWord, tailWord_482410, baseEnd_482410] using wordTrace_append hprefix tailTrace_482410
  have hstable : (prefixWord ++ tailWord_482410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482410).length < 2 ^ (prefixWord ++ tailWord_482410).sum := by decide
  have hdescent : baseEnd_482410 < baseStart_482410 := by decide
  rcases family_descends (prefixWord ++ tailWord_482410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482440 : List Nat := [2, 1, 3, 4, 2, 2, 2, 7]
def baseStart_482440 : Nat := 118140960795 + 482440 * 2 ^ 59
def prefixEnd_482440 : Nat := 4983230072969 + 3 ^ 40 * 482440 * 2
def baseEnd_482440 : Nat := 9174948405748062406715

theorem tailTrace_482440 : CollatzResearch.WordTrace tailWord_482440 prefixEnd_482440 9174948405748062406715 := by
  unfold tailWord_482440
  simp only [CollatzResearch.WordTrace]
  refine ⟨8798016186104874518686387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11730688248139832691581849 8798016186104874518686387)
  ·
    refine ⟨13197024279157311778029581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8798016186104874518686387 13197024279157311778029581)
    ·
      refine ⟨4948884104683991916761093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13197024279157311778029581 4948884104683991916761093)
      ·
        refine ⟨927915769628248484392705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4948884104683991916761093 927915769628248484392705)
        ·
          refine ⟨695936827221186363294529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 927915769628248484392705 695936827221186363294529)
          ·
            refine ⟨521952620415889772470897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695936827221186363294529 521952620415889772470897)
            ·
              refine ⟨391464465311917329353173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521952620415889772470897 391464465311917329353173)
              ·
                refine ⟨9174948405748062406715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 391464465311917329353173 9174948405748062406715)
                ·
                  rfl

theorem cell23_482440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 7].length) (baseStart_482440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482440 prefixEnd_482440 := by exact prefixLift 482440
  have htrace : WordTrace (prefixWord ++ tailWord_482440) baseStart_482440 baseEnd_482440 := by
    simpa [prefixWord, tailWord_482440, baseEnd_482440] using wordTrace_append hprefix tailTrace_482440
  have hstable : (prefixWord ++ tailWord_482440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482440).length < 2 ^ (prefixWord ++ tailWord_482440).sum := by decide
  have hdescent : baseEnd_482440 < baseStart_482440 := by decide
  rcases family_descends (prefixWord ++ tailWord_482440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482443 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 3, 3, 2]
def baseStart_482443 : Nat := 118140960795 + 482443 * 2 ^ 59
def prefixEnd_482443 : Nat := 4983230072969 + 3 ^ 40 * 482443 * 2
def baseEnd_482443 : Nat := 247725147397161173243791

theorem tailTrace_482443 : CollatzResearch.WordTrace tailWord_482443 prefixEnd_482443 247725147397161173243791 := by
  unfold tailWord_482443
  simp only [CollatzResearch.WordTrace]
  refine ⟨17596141791198880549731983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11730761194132587033154655 17596141791198880549731983)
  ·
    refine ⟨26394212686798320824597975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17596141791198880549731983 26394212686798320824597975)
    ·
      refine ⟨39591319030197481236896963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26394212686798320824597975 39591319030197481236896963)
      ·
        refine ⟨59386978545296221855345445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39591319030197481236896963 59386978545296221855345445)
        ·
          refine ⟨11135058477243041597877271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59386978545296221855345445 11135058477243041597877271)
          ·
            refine ⟨16702587715864562396815907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11135058477243041597877271 16702587715864562396815907)
            ·
              refine ⟨25053881573796843595223861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16702587715864562396815907 25053881573796843595223861)
              ·
                refine ⟨2348801397543454087052237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25053881573796843595223861 2348801397543454087052237)
                ·
                  refine ⟨880800524078795282644589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2348801397543454087052237 880800524078795282644589)
                  ·
                    refine ⟨330300196529548230991721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 880800524078795282644589 330300196529548230991721)
                    ·
                      refine ⟨247725147397161173243791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 330300196529548230991721 247725147397161173243791)
                      ·
                        rfl

theorem cell23_482443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 3, 2].length) (baseStart_482443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482443 prefixEnd_482443 := by exact prefixLift 482443
  have htrace : WordTrace (prefixWord ++ tailWord_482443) baseStart_482443 baseEnd_482443 := by
    simpa [prefixWord, tailWord_482443, baseEnd_482443] using wordTrace_append hprefix tailTrace_482443
  have hstable : (prefixWord ++ tailWord_482443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482443).length < 2 ^ (prefixWord ++ tailWord_482443).sum := by decide
  have hdescent : baseEnd_482443 < baseStart_482443 := by decide
  rcases family_descends (prefixWord ++ tailWord_482443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482450 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_482450 : Nat := 118140960795 + 482450 * 2 ^ 59
def prefixEnd_482450 : Nat := 4983230072969 + 3 ^ 40 * 482450 * 2
def baseEnd_482450 : Nat := 247728741761742645856259

theorem tailTrace_482450 : CollatzResearch.WordTrace tailWord_482450 prefixEnd_482450 247728741761742645856259 := by
  unfold tailWord_482450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4399099275543380186309201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11730931401449013830157869 4399099275543380186309201)
  ·
    refine ⟨3299324456657535139731901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4399099275543380186309201 3299324456657535139731901)
    ·
      refine ⟨1237246671246575677399463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3299324456657535139731901 1237246671246575677399463)
      ·
        refine ⟨1855870006869863516099195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1237246671246575677399463 1855870006869863516099195)
        ·
          refine ⟨2783805010304795274148793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1855870006869863516099195 2783805010304795274148793)
          ·
            refine ⟨2087853757728596455611595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2783805010304795274148793 2087853757728596455611595)
            ·
              refine ⟨3131780636592894683417393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087853757728596455611595 3131780636592894683417393)
              ·
                refine ⟨2348835477444671012563045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3131780636592894683417393 2348835477444671012563045)
                ·
                  refine ⟨440406652020875814855571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2348835477444671012563045 440406652020875814855571)
                  ·
                    refine ⟨660609978031313722283357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 440406652020875814855571 660609978031313722283357)
                    ·
                      refine ⟨247728741761742645856259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 660609978031313722283357 247728741761742645856259)
                      ·
                        rfl

theorem cell23_482450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_482450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482450 prefixEnd_482450 := by exact prefixLift 482450
  have htrace : WordTrace (prefixWord ++ tailWord_482450) baseStart_482450 baseEnd_482450 := by
    simpa [prefixWord, tailWord_482450, baseEnd_482450] using wordTrace_append hprefix tailTrace_482450
  have hstable : (prefixWord ++ tailWord_482450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482450).length < 2 ^ (prefixWord ++ tailWord_482450).sum := by decide
  have hdescent : baseEnd_482450 < baseStart_482450 := by decide
  rcases family_descends (prefixWord ++ tailWord_482450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482494 : List Nat := [4, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_482494 : Nat := 118140960795 + 482494 * 2 ^ 59
def prefixEnd_482494 : Nat := 4983230072969 + 3 ^ 40 * 482494 * 2
def baseEnd_482494 : Nat := 247751334910540473706057

theorem tailTrace_482494 : CollatzResearch.WordTrace tailWord_482494 prefixEnd_482494 247751334910540473706057 := by
  unfold tailWord_482494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2199750239251764532479817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11732001276009410839892357 2199750239251764532479817)
  ·
    refine ⟨1649812679438823399359863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2199750239251764532479817 1649812679438823399359863)
    ·
      refine ⟨2474719019158235099039795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1649812679438823399359863 2474719019158235099039795)
      ·
        refine ⟨3712078528737352648559693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2474719019158235099039795 3712078528737352648559693)
        ·
          refine ⟨1392029448276507243209885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3712078528737352648559693 1392029448276507243209885)
          ·
            refine ⟨522011043103690216203707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1392029448276507243209885 522011043103690216203707)
            ·
              refine ⟨783016564655535324305561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522011043103690216203707 783016564655535324305561)
              ·
                refine ⟨587262423491651493229171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783016564655535324305561 587262423491651493229171)
                ·
                  refine ⟨880893635237477239843757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587262423491651493229171 880893635237477239843757)
                  ·
                    refine ⟨330335113214053964941409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 880893635237477239843757 330335113214053964941409)
                    ·
                      refine ⟨247751334910540473706057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 330335113214053964941409 247751334910540473706057)
                      ·
                        rfl

theorem cell23_482494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_482494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482494 prefixEnd_482494 := by exact prefixLift 482494
  have htrace : WordTrace (prefixWord ++ tailWord_482494) baseStart_482494 baseEnd_482494 := by
    simpa [prefixWord, tailWord_482494, baseEnd_482494] using wordTrace_append hprefix tailTrace_482494
  have hstable : (prefixWord ++ tailWord_482494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482494).length < 2 ^ (prefixWord ++ tailWord_482494).sum := by decide
  have hdescent : baseEnd_482494 < baseStart_482494 := by decide
  rcases family_descends (prefixWord ++ tailWord_482494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482513 : List Nat := [1, 2, 2, 1, 2, 2, 1, 7, 5]
def baseStart_482513 : Nat := 118140960795 + 482513 * 2 ^ 59
def prefixEnd_482513 : Nat := 4983230072969 + 3 ^ 40 * 482513 * 2
def baseEnd_482513 : Nat := 27529010115886211040941

theorem tailTrace_482513 : CollatzResearch.WordTrace tailWord_482513 prefixEnd_482513 27529010115886211040941 := by
  unfold tailWord_482513
  simp only [CollatzResearch.WordTrace]
  refine ⟨17598694900945282504780193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11732463267296855003186795 17598694900945282504780193)
  ·
    refine ⟨13199021175708961878585145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17598694900945282504780193 13199021175708961878585145)
    ·
      refine ⟨9899265881781721408938859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13199021175708961878585145 9899265881781721408938859)
      ·
        refine ⟨14848898822672582113408289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9899265881781721408938859 14848898822672582113408289)
        ·
          refine ⟨11136674117004436585056217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14848898822672582113408289 11136674117004436585056217)
          ·
            refine ⟨8352505587753327438792163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11136674117004436585056217 8352505587753327438792163)
            ·
              refine ⟨12528758381629991158188245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8352505587753327438792163 12528758381629991158188245)
              ·
                refine ⟨293642774569452917770037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12528758381629991158188245 293642774569452917770037)
                ·
                  refine ⟨27529010115886211040941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 293642774569452917770037 27529010115886211040941)
                  ·
                    rfl

theorem cell23_482513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 5].length) (baseStart_482513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482513 prefixEnd_482513 := by exact prefixLift 482513
  have htrace : WordTrace (prefixWord ++ tailWord_482513) baseStart_482513 baseEnd_482513 := by
    simpa [prefixWord, tailWord_482513, baseEnd_482513] using wordTrace_append hprefix tailTrace_482513
  have hstable : (prefixWord ++ tailWord_482513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482513).length < 2 ^ (prefixWord ++ tailWord_482513).sum := by decide
  have hdescent : baseEnd_482513 < baseStart_482513 := by decide
  rcases family_descends (prefixWord ++ tailWord_482513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482550 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_482550 : Nat := 118140960795 + 482550 * 2 ^ 59
def prefixEnd_482550 : Nat := 4983230072969 + 3 ^ 40 * 482550 * 2
def baseEnd_482550 : Nat := 247780089827192254605799

theorem tailTrace_482550 : CollatzResearch.WordTrace tailWord_482550 prefixEnd_482550 247780089827192254605799 := by
  unfold tailWord_482550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100002775113202363992319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11733362934540825215918069 1100002775113202363992319)
  ·
    refine ⟨1650004162669803545988479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1100002775113202363992319 1650004162669803545988479)
    ·
      refine ⟨2475006244004705318982719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1650004162669803545988479 2475006244004705318982719)
      ·
        refine ⟨3712509366007057978474079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2475006244004705318982719 3712509366007057978474079)
        ·
          refine ⟨5568764049010586967711119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3712509366007057978474079 5568764049010586967711119)
          ·
            refine ⟨8353146073515880451566679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568764049010586967711119 8353146073515880451566679)
            ·
              refine ⟨12529719110273820677350019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353146073515880451566679 12529719110273820677350019)
              ·
                refine ⟨18794578665410731016025029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12529719110273820677350019 18794578665410731016025029)
                ·
                  refine ⟨3523983499764512065504693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18794578665410731016025029 3523983499764512065504693)
                  ·
                    refine ⟨330373453102923006141065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3523983499764512065504693 330373453102923006141065)
                    ·
                      refine ⟨247780089827192254605799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 330373453102923006141065 247780089827192254605799)
                      ·
                        rfl

theorem cell23_482550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_482550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482550 prefixEnd_482550 := by exact prefixLift 482550
  have htrace : WordTrace (prefixWord ++ tailWord_482550) baseStart_482550 baseEnd_482550 := by
    simpa [prefixWord, tailWord_482550, baseEnd_482550] using wordTrace_append hprefix tailTrace_482550
  have hstable : (prefixWord ++ tailWord_482550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482550).length < 2 ^ (prefixWord ++ tailWord_482550).sum := by decide
  have hdescent : baseEnd_482550 < baseStart_482550 := by decide
  rcases family_descends (prefixWord ++ tailWord_482550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482563 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 4]
def baseStart_482563 : Nat := 118140960795 + 482563 * 2 ^ 59
def prefixEnd_482563 : Nat := 4983230072969 + 3 ^ 40 * 482563 * 2
def baseEnd_482563 : Nat := 247786765075700703743239

theorem tailTrace_482563 : CollatzResearch.WordTrace tailWord_482563 prefixEnd_482563 247786765075700703743239 := by
  unfold tailWord_482563
  simp only [CollatzResearch.WordTrace]
  refine ⟨17600518550764141044100343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11733679033842760696066895 17600518550764141044100343)
  ·
    refine ⟨26400777826146211566150515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17600518550764141044100343 26400777826146211566150515)
    ·
      refine ⟨39601166739219317349225773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26400777826146211566150515 39601166739219317349225773)
      ·
        refine ⟨14850437527207244005959665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39601166739219317349225773 14850437527207244005959665)
        ·
          refine ⟨11137828145405433004469749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14850437527207244005959665 11137828145405433004469749)
          ·
            refine ⟨1044171388631759344169039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11137828145405433004469749 1044171388631759344169039)
            ·
              refine ⟨1566257082947639016253559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044171388631759344169039 1566257082947639016253559)
              ·
                refine ⟨2349385624421458524380339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1566257082947639016253559 2349385624421458524380339)
                ·
                  refine ⟨3524078436632187786570509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349385624421458524380339 3524078436632187786570509)
                  ·
                    refine ⟨1321529413737070419963941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3524078436632187786570509 1321529413737070419963941)
                    ·
                      refine ⟨247786765075700703743239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1321529413737070419963941 247786765075700703743239)
                      ·
                        rfl

theorem cell23_482563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_482563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482563 prefixEnd_482563 := by exact prefixLift 482563
  have htrace : WordTrace (prefixWord ++ tailWord_482563) baseStart_482563 baseEnd_482563 := by
    simpa [prefixWord, tailWord_482563, baseEnd_482563] using wordTrace_append hprefix tailTrace_482563
  have hstable : (prefixWord ++ tailWord_482563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482563).length < 2 ^ (prefixWord ++ tailWord_482563).sum := by decide
  have hdescent : baseEnd_482563 < baseStart_482563 := by decide
  rcases family_descends (prefixWord ++ tailWord_482563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482600 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_482600 : Nat := 118140960795 + 482600 * 2 ^ 59
def prefixEnd_482600 : Nat := 4983230072969 + 3 ^ 40 * 482600 * 2
def baseEnd_482600 : Nat := 247805763859917058980569

theorem tailTrace_482600 : CollatzResearch.WordTrace tailWord_482600 prefixEnd_482600 247805763859917058980569 := by
  unfold tailWord_482600
  simp only [CollatzResearch.WordTrace]
  refine ⟨8800934025815048181598627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11734578701086730908798169 8800934025815048181598627)
  ·
    refine ⟨13201401038722572272397941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8800934025815048181598627 13201401038722572272397941)
    ·
      refine ⟨1237631347380241150537307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13201401038722572272397941 1237631347380241150537307)
      ·
        refine ⟨1856447021070361725805961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1237631347380241150537307 1856447021070361725805961)
        ·
          refine ⟨1392335265802771294354471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1856447021070361725805961 1392335265802771294354471)
          ·
            refine ⟨2088502898704156941531707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1392335265802771294354471 2088502898704156941531707)
            ·
              refine ⟨3132754348056235412297561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2088502898704156941531707 3132754348056235412297561)
              ·
                refine ⟨2349565761042176559223171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132754348056235412297561 2349565761042176559223171)
                ·
                  refine ⟨3524348641563264838834757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349565761042176559223171 3524348641563264838834757)
                  ·
                    refine ⟨660815370293112157281517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3524348641563264838834757 660815370293112157281517)
                    ·
                      refine ⟨247805763859917058980569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 660815370293112157281517 247805763859917058980569)
                      ·
                        rfl

theorem cell23_482600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_482600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482600 prefixEnd_482600 := by exact prefixLift 482600
  have htrace : WordTrace (prefixWord ++ tailWord_482600) baseStart_482600 baseEnd_482600 := by
    simpa [prefixWord, tailWord_482600, baseEnd_482600] using wordTrace_append hprefix tailTrace_482600
  have hstable : (prefixWord ++ tailWord_482600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482600).length < 2 ^ (prefixWord ++ tailWord_482600).sum := by decide
  have hdescent : baseEnd_482600 < baseStart_482600 := by decide
  rcases family_descends (prefixWord ++ tailWord_482600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482647 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 3, 1, 3]
def baseStart_482647 : Nat := 118140960795 + 482647 * 2 ^ 59
def prefixEnd_482647 : Nat := 4983230072969 + 3 ^ 40 * 482647 * 2
def baseEnd_482647 : Nat := 247829897450678375092853

theorem tailTrace_482647 : CollatzResearch.WordTrace tailWord_482647 prefixEnd_482647 247829897450678375092853 := by
  unfold tailWord_482647
  simp only [CollatzResearch.WordTrace]
  refine ⟨17603582282459823390158195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11735721521639882260105463 17603582282459823390158195)
  ·
    refine ⟨26405373423689735085237293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17603582282459823390158195 26405373423689735085237293)
    ·
      refine ⟨9902015033883650656963985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26405373423689735085237293 9902015033883650656963985)
      ·
        refine ⟨7426511275412737992722989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9902015033883650656963985 7426511275412737992722989)
        ·
          refine ⟨2784941728279776747271121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7426511275412737992722989 2784941728279776747271121)
          ·
            refine ⟨2088706296209832560453341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2784941728279776747271121 2088706296209832560453341)
            ·
              refine ⟨783264861078687210170003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2088706296209832560453341 783264861078687210170003)
              ·
                refine ⟨1174897291618030815255005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783264861078687210170003 1174897291618030815255005)
                ·
                  refine ⟨440586484356761555720627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1174897291618030815255005 440586484356761555720627)
                  ·
                    refine ⟨660879726535142333580941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 440586484356761555720627 660879726535142333580941)
                    ·
                      refine ⟨247829897450678375092853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 660879726535142333580941 247829897450678375092853)
                      ·
                        rfl

theorem cell23_482647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_482647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482647 prefixEnd_482647 := by exact prefixLift 482647
  have htrace : WordTrace (prefixWord ++ tailWord_482647) baseStart_482647 baseEnd_482647 := by
    simpa [prefixWord, tailWord_482647, baseEnd_482647] using wordTrace_append hprefix tailTrace_482647
  have hstable : (prefixWord ++ tailWord_482647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482647).length < 2 ^ (prefixWord ++ tailWord_482647).sum := by decide
  have hdescent : baseEnd_482647 < baseStart_482647 := by decide
  rcases family_descends (prefixWord ++ tailWord_482647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482673 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_482673 : Nat := 118140960795 + 482673 * 2 ^ 59
def prefixEnd_482673 : Nat := 4983230072969 + 3 ^ 40 * 482673 * 2
def baseEnd_482673 : Nat := 247843247947695273367733

theorem tailTrace_482673 : CollatzResearch.WordTrace tailWord_482673 prefixEnd_482673 247843247947695273367733 := by
  unfold tailWord_482673
  simp only [CollatzResearch.WordTrace]
  refine ⟨17604530580365629830604673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11736353720243753220403115 17604530580365629830604673)
  ·
    refine ⟨13203397935274222372953505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17604530580365629830604673 13203397935274222372953505)
    ·
      refine ⟨9902548451455666779715129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13203397935274222372953505 9902548451455666779715129)
      ·
        refine ⟨7426911338591750084786347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9902548451455666779715129 7426911338591750084786347)
        ·
          refine ⟨11140367007887625127179521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7426911338591750084786347 11140367007887625127179521)
          ·
            refine ⟨8355275255915718845384641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11140367007887625127179521 8355275255915718845384641)
            ·
              refine ⟨6266456441936789134038481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8355275255915718845384641 6266456441936789134038481)
              ·
                refine ⟨4699842331452591850528861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6266456441936789134038481 4699842331452591850528861)
                ·
                  refine ⟨1762440874294721943948323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4699842331452591850528861 1762440874294721943948323)
                  ·
                    refine ⟨2643661311442082915922485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1762440874294721943948323 2643661311442082915922485)
                    ·
                      refine ⟨247843247947695273367733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2643661311442082915922485 247843247947695273367733)
                      ·
                        rfl

theorem cell23_482673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_482673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482673 prefixEnd_482673 := by exact prefixLift 482673
  have htrace : WordTrace (prefixWord ++ tailWord_482673) baseStart_482673 baseEnd_482673 := by
    simpa [prefixWord, tailWord_482673, baseEnd_482673] using wordTrace_append hprefix tailTrace_482673
  have hstable : (prefixWord ++ tailWord_482673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482673).length < 2 ^ (prefixWord ++ tailWord_482673).sum := by decide
  have hdescent : baseEnd_482673 < baseStart_482673 := by decide
  rcases family_descends (prefixWord ++ tailWord_482673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482717 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_482717 : Nat := 118140960795 + 482717 * 2 ^ 59
def prefixEnd_482717 : Nat := 4983230072969 + 3 ^ 40 * 482717 * 2
def baseEnd_482717 : Nat := 247865841096493101217531

theorem tailTrace_482717 : CollatzResearch.WordTrace tailWord_482717 prefixEnd_482717 247865841096493101217531 := by
  unfold tailWord_482717
  simp only [CollatzResearch.WordTrace]
  refine ⟨17606135392206225345206405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11737423594804150230137603 17606135392206225345206405)
  ·
    refine ⟨3301150386038667252226201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17606135392206225345206405 3301150386038667252226201)
    ·
      refine ⟨2475862789529000439169651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3301150386038667252226201 2475862789529000439169651)
      ·
        refine ⟨3713794184293500658754477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2475862789529000439169651 3713794184293500658754477)
        ·
          refine ⟨1392672819110062747032929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3713794184293500658754477 1392672819110062747032929)
          ·
            refine ⟨1044504614332547060274697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1392672819110062747032929 1044504614332547060274697)
            ·
              refine ⟨783378460749410295206023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044504614332547060274697 783378460749410295206023)
              ·
                refine ⟨1175067691124115442809035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783378460749410295206023 1175067691124115442809035)
                ·
                  refine ⟨1762601536686173164213553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175067691124115442809035 1762601536686173164213553)
                  ·
                    refine ⟨1321951152514629873160165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1762601536686173164213553 1321951152514629873160165)
                    ·
                      refine ⟨247865841096493101217531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1321951152514629873160165 247865841096493101217531)
                      ·
                        rfl

theorem cell23_482717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_482717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482717 prefixEnd_482717 := by exact prefixLift 482717
  have htrace : WordTrace (prefixWord ++ tailWord_482717) baseStart_482717 baseEnd_482717 := by
    simpa [prefixWord, tailWord_482717, baseEnd_482717] using wordTrace_append hprefix tailTrace_482717
  have hstable : (prefixWord ++ tailWord_482717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482717).length < 2 ^ (prefixWord ++ tailWord_482717).sum := by decide
  have hdescent : baseEnd_482717 < baseStart_482717 := by decide
  rcases family_descends (prefixWord ++ tailWord_482717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482723 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 2, 7]
def baseStart_482723 : Nat := 118140960795 + 482723 * 2 ^ 59
def prefixEnd_482723 : Nat := 4983230072969 + 3 ^ 40 * 482723 * 2
def baseEnd_482723 : Nat := 82622973993473359247501

theorem tailTrace_482723 : CollatzResearch.WordTrace tailWord_482723 prefixEnd_482723 82622973993473359247501 := by
  unfold tailWord_482723
  simp only [CollatzResearch.WordTrace]
  refine ⟨17606354230184488369924823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11737569486789658913283215 17606354230184488369924823)
  ·
    refine ⟨26409531345276732554887235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17606354230184488369924823 26409531345276732554887235)
    ·
      refine ⟨39614297017915098832330853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26409531345276732554887235 39614297017915098832330853)
      ·
        refine ⟨7427680690859081031062035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39614297017915098832330853 7427680690859081031062035)
        ·
          refine ⟨11141521036288621546593053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7427680690859081031062035 11141521036288621546593053)
          ·
            refine ⟨4178070388608233079972395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11141521036288621546593053 4178070388608233079972395)
            ·
              refine ⟨6267105582912349619958593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178070388608233079972395 6267105582912349619958593)
              ·
                refine ⟨4700329187184262214968945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6267105582912349619958593 4700329187184262214968945)
                ·
                  refine ⟨3525246890388196661226709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4700329187184262214968945 3525246890388196661226709)
                  ·
                    refine ⟨82622973993473359247501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3525246890388196661226709 82622973993473359247501)
                    ·
                      rfl

theorem cell23_482723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 7].length) (baseStart_482723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482723 prefixEnd_482723 := by exact prefixLift 482723
  have htrace : WordTrace (prefixWord ++ tailWord_482723) baseStart_482723 baseEnd_482723 := by
    simpa [prefixWord, tailWord_482723, baseEnd_482723] using wordTrace_append hprefix tailTrace_482723
  have hstable : (prefixWord ++ tailWord_482723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482723).length < 2 ^ (prefixWord ++ tailWord_482723).sum := by decide
  have hdescent : baseEnd_482723 < baseStart_482723 := by decide
  rcases family_descends (prefixWord ++ tailWord_482723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482737 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 4, 1, 3]
def baseStart_482737 : Nat := 118140960795 + 482737 * 2 ^ 59
def prefixEnd_482737 : Nat := 4983230072969 + 3 ^ 40 * 482737 * 2
def baseEnd_482737 : Nat := 247876110709583022967439

theorem tailTrace_482737 : CollatzResearch.WordTrace tailWord_482737 prefixEnd_482737 247876110709583022967439 := by
  unfold tailWord_482737
  simp only [CollatzResearch.WordTrace]
  refine ⟨17606864852133768760934465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11737909901422512507289643 17606864852133768760934465)
  ·
    refine ⟨13205148639100326570700849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17606864852133768760934465 13205148639100326570700849)
    ·
      refine ⟨9903861479325244928025637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13205148639100326570700849 9903861479325244928025637)
      ·
        refine ⟨1856974027373483424004807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9903861479325244928025637 1856974027373483424004807)
        ·
          refine ⟨2785461041060225136007211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856974027373483424004807 2785461041060225136007211)
          ·
            refine ⟨4178191561590337704010817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785461041060225136007211 4178191561590337704010817)
            ·
              refine ⟨3133643671192753278008113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4178191561590337704010817 3133643671192753278008113)
              ·
                refine ⟨2350232753394564958506085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3133643671192753278008113 2350232753394564958506085)
                ·
                  refine ⟨440668641261480929719891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2350232753394564958506085 440668641261480929719891)
                  ·
                    refine ⟨661002961892221394579837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 440668641261480929719891 661002961892221394579837)
                    ·
                      refine ⟨247876110709583022967439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 661002961892221394579837 247876110709583022967439)
                      ·
                        rfl

theorem cell23_482737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_482737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482737 prefixEnd_482737 := by exact prefixLift 482737
  have htrace : WordTrace (prefixWord ++ tailWord_482737) baseStart_482737 baseEnd_482737 := by
    simpa [prefixWord, tailWord_482737, baseEnd_482737] using wordTrace_append hprefix tailTrace_482737
  have hstable : (prefixWord ++ tailWord_482737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482737).length < 2 ^ (prefixWord ++ tailWord_482737).sum := by decide
  have hdescent : baseEnd_482737 < baseStart_482737 := by decide
  rcases family_descends (prefixWord ++ tailWord_482737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482741 : List Nat := [1, 3, 3, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_482741 : Nat := 118140960795 + 482741 * 2 ^ 59
def prefixEnd_482741 : Nat := 4983230072969 + 3 ^ 40 * 482741 * 2
def baseEnd_482741 : Nat := 247878164632201007317421

theorem tailTrace_482741 : CollatzResearch.WordTrace tailWord_482741 prefixEnd_482741 247878164632201007317421 := by
  unfold tailWord_482741
  simp only [CollatzResearch.WordTrace]
  refine ⟨17607010744119277444080077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11738007162746184962720051 17607010744119277444080077)
  ·
    refine ⟨6602629029044729041530029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17607010744119277444080077 6602629029044729041530029)
    ·
      refine ⟨2475985885891773390573761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6602629029044729041530029 2475985885891773390573761)
      ·
        refine ⟨1856989414418830042930321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2475985885891773390573761 1856989414418830042930321)
        ·
          refine ⟨1392742060814122532197741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1856989414418830042930321 1392742060814122532197741)
          ·
            refine ⟨522278272805295949574153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1392742060814122532197741 522278272805295949574153)
            ·
              refine ⟨391708704603971962180615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522278272805295949574153 391708704603971962180615)
              ·
                refine ⟨587563056905957943270923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391708704603971962180615 587563056905957943270923)
                ·
                  refine ⟨881344585358936914906385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587563056905957943270923 881344585358936914906385)
                  ·
                    refine ⟨661008439019202686179789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 881344585358936914906385 661008439019202686179789)
                    ·
                      refine ⟨247878164632201007317421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 661008439019202686179789 247878164632201007317421)
                      ·
                        rfl

theorem cell23_482741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_482741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482741 prefixEnd_482741 := by exact prefixLift 482741
  have htrace : WordTrace (prefixWord ++ tailWord_482741) baseStart_482741 baseEnd_482741 := by
    simpa [prefixWord, tailWord_482741, baseEnd_482741] using wordTrace_append hprefix tailTrace_482741
  have hstable : (prefixWord ++ tailWord_482741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482741).length < 2 ^ (prefixWord ++ tailWord_482741).sum := by decide
  have hdescent : baseEnd_482741 < baseStart_482741 := by decide
  rcases family_descends (prefixWord ++ tailWord_482741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482781 : List Nat := [1, 4, 3, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_482781 : Nat := 118140960795 + 482781 * 2 ^ 59
def prefixEnd_482781 : Nat := 4983230072969 + 3 ^ 40 * 482781 * 2
def baseEnd_482781 : Nat := 247898703858380850817237

theorem tailTrace_482781 : CollatzResearch.WordTrace tailWord_482781 prefixEnd_482781 247898703858380850817237 := by
  unfold tailWord_482781
  simp only [CollatzResearch.WordTrace]
  refine ⟨17608469663974364275536197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11738979775982909517024131 17608469663974364275536197)
  ·
    refine ⟨3301588061995193301663037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17608469663974364275536197 3301588061995193301663037)
    ·
      refine ⟨1238095523248197488123639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3301588061995193301663037 1238095523248197488123639)
      ·
        refine ⟨1857143284872296232185459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238095523248197488123639 1857143284872296232185459)
        ·
          refine ⟨2785714927308444348278189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857143284872296232185459 2785714927308444348278189)
          ·
            refine ⟨1044643097740666630604321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2785714927308444348278189 1044643097740666630604321)
            ·
              refine ⟨783482323305499972953241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044643097740666630604321 783482323305499972953241)
              ·
                refine ⟨587611742479124979714931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783482323305499972953241 587611742479124979714931)
                ·
                  refine ⟨881417613718687469572397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587611742479124979714931 881417613718687469572397)
                  ·
                    refine ⟨330531605144507801089649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 881417613718687469572397 330531605144507801089649)
                    ·
                      refine ⟨247898703858380850817237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 330531605144507801089649 247898703858380850817237)
                      ·
                        rfl

theorem cell23_482781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_482781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482781 prefixEnd_482781 := by exact prefixLift 482781
  have htrace : WordTrace (prefixWord ++ tailWord_482781) baseStart_482781 baseEnd_482781 := by
    simpa [prefixWord, tailWord_482781, baseEnd_482781] using wordTrace_append hprefix tailTrace_482781
  have hstable : (prefixWord ++ tailWord_482781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482781).length < 2 ^ (prefixWord ++ tailWord_482781).sum := by decide
  have hdescent : baseEnd_482781 < baseStart_482781 := by decide
  rcases family_descends (prefixWord ++ tailWord_482781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482867 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 4]
def baseStart_482867 : Nat := 118140960795 + 482867 * 2 ^ 59
def prefixEnd_482867 : Nat := 4983230072969 + 3 ^ 40 * 482867 * 2
def baseEnd_482867 : Nat := 247942863194667514341841

theorem tailTrace_482867 : CollatzResearch.WordTrace tailWord_482867 prefixEnd_482867 247942863194667514341841 := by
  unfold tailWord_482867
  simp only [CollatzResearch.WordTrace]
  refine ⟨17611606341662800963166855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11741070894441867308777903 17611606341662800963166855)
  ·
    refine ⟨26417409512494201444750283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17611606341662800963166855 26417409512494201444750283)
    ·
      refine ⟨39626114268741302167125425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26417409512494201444750283 39626114268741302167125425)
      ·
        refine ⟨29719585701555976625344069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39626114268741302167125425 29719585701555976625344069)
        ·
          refine ⟨5572422319041745617252013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29719585701555976625344069 5572422319041745617252013)
          ·
            refine ⟨2089658369640654606469505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5572422319041745617252013 2089658369640654606469505)
            ·
              refine ⟨1567243777230490954852129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2089658369640654606469505 1567243777230490954852129)
              ·
                refine ⟨1175432832922868216139097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1567243777230490954852129 1175432832922868216139097)
                ·
                  refine ⟨881574624692151162104323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1175432832922868216139097 881574624692151162104323)
                  ·
                    refine ⟨1322361937038226743156485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 881574624692151162104323 1322361937038226743156485)
                    ·
                      refine ⟨247942863194667514341841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1322361937038226743156485 247942863194667514341841)
                      ·
                        rfl

theorem cell23_482867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_482867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482867 prefixEnd_482867 := by exact prefixLift 482867
  have htrace : WordTrace (prefixWord ++ tailWord_482867) baseStart_482867 baseEnd_482867 := by
    simpa [prefixWord, tailWord_482867, baseEnd_482867] using wordTrace_append hprefix tailTrace_482867
  have hstable : (prefixWord ++ tailWord_482867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482867).length < 2 ^ (prefixWord ++ tailWord_482867).sum := by decide
  have hdescent : baseEnd_482867 < baseStart_482867 := by decide
  rcases family_descends (prefixWord ++ tailWord_482867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482880 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 4]
def baseStart_482880 : Nat := 118140960795 + 482880 * 2 ^ 59
def prefixEnd_482880 : Nat := 4983230072969 + 3 ^ 40 * 482880 * 2
def baseEnd_482880 : Nat := 247949538443175963479281

theorem tailTrace_482880 : CollatzResearch.WordTrace tailWord_482880 prefixEnd_482880 247949538443175963479281 := by
  unfold tailWord_482880
  simp only [CollatzResearch.WordTrace]
  refine ⟨8806040245307852091695047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11741386993743802788926729 8806040245307852091695047)
  ·
    refine ⟨13209060367961778137542571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8806040245307852091695047 13209060367961778137542571)
    ·
      refine ⟨19813590551942667206313857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13209060367961778137542571 19813590551942667206313857)
      ·
        refine ⟨14860192913957000404735393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19813590551942667206313857 14860192913957000404735393)
        ·
          refine ⟨11145144685467750303551545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14860192913957000404735393 11145144685467750303551545)
          ·
            refine ⟨8358858514100812727663659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11145144685467750303551545 8358858514100812727663659)
            ·
              refine ⟨12538287771151219091495489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8358858514100812727663659 12538287771151219091495489)
              ·
                refine ⟨9403715828363414318621617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12538287771151219091495489 9403715828363414318621617)
                ·
                  refine ⟨7052786871272560738966213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9403715828363414318621617 7052786871272560738966213)
                  ·
                    refine ⟨1322397538363605138556165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7052786871272560738966213 1322397538363605138556165)
                    ·
                      refine ⟨247949538443175963479281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1322397538363605138556165 247949538443175963479281)
                      ·
                        rfl

theorem cell23_482880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_482880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482880 prefixEnd_482880 := by exact prefixLift 482880
  have htrace : WordTrace (prefixWord ++ tailWord_482880) baseStart_482880 baseEnd_482880 := by
    simpa [prefixWord, tailWord_482880, baseEnd_482880] using wordTrace_append hprefix tailTrace_482880
  have hstable : (prefixWord ++ tailWord_482880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482880).length < 2 ^ (prefixWord ++ tailWord_482880).sum := by decide
  have hdescent : baseEnd_482880 < baseStart_482880 := by decide
  rcases family_descends (prefixWord ++ tailWord_482880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482954 : List Nat := [3, 1, 2, 3, 2, 1, 1, 4, 1, 5]
def baseStart_482954 : Nat := 118140960795 + 482954 * 2 ^ 59
def prefixEnd_482954 : Nat := 4983230072969 + 3 ^ 40 * 482954 * 2
def baseEnd_482954 : Nat := 82662512003869557984647

theorem tailTrace_482954 : CollatzResearch.WordTrace tailWord_482954 prefixEnd_482954 82662512003869557984647 := by
  unfold tailWord_482954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4403694873086903705395979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11743186328231743214389277 4403694873086903705395979)
  ·
    refine ⟨6605542309630355558093969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4403694873086903705395979 6605542309630355558093969)
    ·
      refine ⟨4954156732222766668570477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6605542309630355558093969 4954156732222766668570477)
      ·
        refine ⟨1857808774583537500713929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4954156732222766668570477 1857808774583537500713929)
        ·
          refine ⟨1393356580937653125535447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1857808774583537500713929 1393356580937653125535447)
          ·
            refine ⟨2090034871406479688303171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393356580937653125535447 2090034871406479688303171)
            ·
              refine ⟨3135052307109719532454757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090034871406479688303171 3135052307109719532454757)
              ·
                refine ⟨587822307583072412335267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3135052307109719532454757 587822307583072412335267)
                ·
                  refine ⟨881733461374608618502901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587822307583072412335267 881733461374608618502901)
                  ·
                    refine ⟨82662512003869557984647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 881733461374608618502901 82662512003869557984647)
                    ·
                      rfl

theorem cell23_482954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_482954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482954 prefixEnd_482954 := by exact prefixLift 482954
  have htrace : WordTrace (prefixWord ++ tailWord_482954) baseStart_482954 baseEnd_482954 := by
    simpa [prefixWord, tailWord_482954, baseEnd_482954] using wordTrace_append hprefix tailTrace_482954
  have hstable : (prefixWord ++ tailWord_482954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482954).length < 2 ^ (prefixWord ++ tailWord_482954).sum := by decide
  have hdescent : baseEnd_482954 < baseStart_482954 := by decide
  rcases family_descends (prefixWord ++ tailWord_482954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482968 : List Nat := [2, 1, 2, 4, 1, 2, 3, 3, 1, 1, 3]
def baseStart_482968 : Nat := 118140960795 + 482968 * 2 ^ 59
def prefixEnd_482968 : Nat := 4983230072969 + 3 ^ 40 * 482968 * 2
def baseEnd_482968 : Nat := 247994724740771619178877

theorem tailTrace_482968 : CollatzResearch.WordTrace tailWord_482968 prefixEnd_482968 247994724740771619178877 := by
  unfold tailWord_482968
  simp only [CollatzResearch.WordTrace]
  refine ⟨8807645057148447606296779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11743526742864596808395705 8807645057148447606296779)
  ·
    refine ⟨13211467585722671409445169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8807645057148447606296779 13211467585722671409445169)
    ·
      refine ⟨9908600689292003557083877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13211467585722671409445169 9908600689292003557083877)
      ·
        refine ⟨1857862629242250666953227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9908600689292003557083877 1857862629242250666953227)
        ·
          refine ⟨2786793943863376000429841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857862629242250666953227 2786793943863376000429841)
          ·
            refine ⟨2090095457897532000322381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2786793943863376000429841 2090095457897532000322381)
            ·
              refine ⟨783785796711574500120893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2090095457897532000322381 783785796711574500120893)
              ·
                refine ⟨293919673766840437545335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 783785796711574500120893 293919673766840437545335)
                ·
                  refine ⟨440879510650260656318003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293919673766840437545335 440879510650260656318003)
                  ·
                    refine ⟨661319265975390984477005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 440879510650260656318003 661319265975390984477005)
                    ·
                      refine ⟨247994724740771619178877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 661319265975390984477005 247994724740771619178877)
                      ·
                        rfl

theorem cell23_482968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_482968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_482968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_482968 prefixEnd_482968 := by exact prefixLift 482968
  have htrace : WordTrace (prefixWord ++ tailWord_482968) baseStart_482968 baseEnd_482968 := by
    simpa [prefixWord, tailWord_482968, baseEnd_482968] using wordTrace_append hprefix tailTrace_482968
  have hstable : (prefixWord ++ tailWord_482968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482968).length < 2 ^ (prefixWord ++ tailWord_482968).sum := by decide
  have hdescent : baseEnd_482968 < baseStart_482968 := by decide
  rcases family_descends (prefixWord ++ tailWord_482968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483001 : List Nat := [1, 2, 1, 4, 1, 1, 6, 1, 2, 4]
def baseStart_483001 : Nat := 118140960795 + 483001 * 2 ^ 59
def prefixEnd_483001 : Nat := 4983230072969 + 3 ^ 40 * 483001 * 2
def baseEnd_483001 : Nat := 82670556534123330022075

theorem tailTrace_483001 : CollatzResearch.WordTrace tailWord_483001 prefixEnd_483001 82670556534123330022075 := by
  unfold tailWord_483001
  simp only [CollatzResearch.WordTrace]
  refine ⟨17616493723177341848544857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11744329148784894565696571 17616493723177341848544857)
  ·
    refine ⟨13212370292383006386408643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17616493723177341848544857 13212370292383006386408643)
    ·
      refine ⟨19818555438574509579612965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13212370292383006386408643 19818555438574509579612965)
      ·
        refine ⟨3715979144732720546177431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19818555438574509579612965 3715979144732720546177431)
        ·
          refine ⟨5573968717099080819266147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3715979144732720546177431 5573968717099080819266147)
          ·
            refine ⟨8360953075648621228899221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5573968717099080819266147 8360953075648621228899221)
            ·
              refine ⟨391919675421029120104651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8360953075648621228899221 391919675421029120104651)
              ·
                refine ⟨587879513131543680156977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391919675421029120104651 587879513131543680156977)
                ·
                  refine ⟨440909634848657760117733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587879513131543680156977 440909634848657760117733)
                  ·
                    refine ⟨82670556534123330022075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 440909634848657760117733 82670556534123330022075)
                    ·
                      rfl

theorem cell23_483001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 2, 4].length) (baseStart_483001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483001 prefixEnd_483001 := by exact prefixLift 483001
  have htrace : WordTrace (prefixWord ++ tailWord_483001) baseStart_483001 baseEnd_483001 := by
    simpa [prefixWord, tailWord_483001, baseEnd_483001] using wordTrace_append hprefix tailTrace_483001
  have hstable : (prefixWord ++ tailWord_483001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483001).length < 2 ^ (prefixWord ++ tailWord_483001).sum := by decide
  have hdescent : baseEnd_483001 < baseStart_483001 := by decide
  rcases family_descends (prefixWord ++ tailWord_483001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483021 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_483021 : Nat := 118140960795 + 483021 * 2 ^ 59
def prefixEnd_483021 : Nat := 4983230072969 + 3 ^ 40 * 483021 * 2
def baseEnd_483021 : Nat := 248021939215459911816133

theorem tailTrace_483021 : CollatzResearch.WordTrace tailWord_483021 prefixEnd_483021 248021939215459911816133 := by
  unfold tailWord_483021
  simp only [CollatzResearch.WordTrace]
  refine ⟨17617223183104885264272917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11744815455403256842848611 17617223183104885264272917)
  ·
    refine ⟨825807336708041496762793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17617223183104885264272917 825807336708041496762793)
    ·
      refine ⟨619355502531031122572095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 825807336708041496762793 619355502531031122572095)
      ·
        refine ⟨929033253796546683858143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619355502531031122572095 929033253796546683858143)
        ·
          refine ⟨1393549880694820025787215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929033253796546683858143 1393549880694820025787215)
          ·
            refine ⟨2090324821042230038680823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393549880694820025787215 2090324821042230038680823)
            ·
              refine ⟨3135487231563345058021235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090324821042230038680823 3135487231563345058021235)
              ·
                refine ⟨4703230847345017587031853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135487231563345058021235 4703230847345017587031853)
                ·
                  refine ⟨1763711567754381595136945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4703230847345017587031853 1763711567754381595136945)
                  ·
                    refine ⟨1322783675815786196352709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1763711567754381595136945 1322783675815786196352709)
                    ·
                      refine ⟨248021939215459911816133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1322783675815786196352709 248021939215459911816133)
                      ·
                        rfl

theorem cell23_483021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_483021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483021 prefixEnd_483021 := by exact prefixLift 483021
  have htrace : WordTrace (prefixWord ++ tailWord_483021) baseStart_483021 baseEnd_483021 := by
    simpa [prefixWord, tailWord_483021, baseEnd_483021] using wordTrace_append hprefix tailTrace_483021
  have hstable : (prefixWord ++ tailWord_483021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483021).length < 2 ^ (prefixWord ++ tailWord_483021).sum := by decide
  have hdescent : baseEnd_483021 < baseStart_483021 := by decide
  rcases family_descends (prefixWord ++ tailWord_483021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483024 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 4, 1, 3]
def baseStart_483024 : Nat := 118140960795 + 483024 * 2 ^ 59
def prefixEnd_483024 : Nat := 4983230072969 + 3 ^ 40 * 483024 * 2
def baseEnd_483024 : Nat := 248023479657423400078619

theorem tailTrace_483024 : CollatzResearch.WordTrace tailWord_483024 prefixEnd_483024 248023479657423400078619 := by
  unfold tailWord_483024
  simp only [CollatzResearch.WordTrace]
  refine ⟨8808666301047008388316063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11744888401396011184421417 8808666301047008388316063)
  ·
    refine ⟨13212999451570512582474095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8808666301047008388316063 13212999451570512582474095)
    ·
      refine ⟨19819499177355768873711143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13212999451570512582474095 19819499177355768873711143)
      ·
        refine ⟨29729248766033653310566715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19819499177355768873711143 29729248766033653310566715)
        ·
          refine ⟨44593873149050479965850073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29729248766033653310566715 44593873149050479965850073)
          ·
            refine ⟨33445404861787859974387555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44593873149050479965850073 33445404861787859974387555)
            ·
              refine ⟨50168107292681789961581333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33445404861787859974387555 50168107292681789961581333)
              ·
                refine ⟨2351630029344458904449125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50168107292681789961581333 2351630029344458904449125)
                ·
                  refine ⟨440930630502086044584211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2351630029344458904449125 440930630502086044584211)
                  ·
                    refine ⟨661395945753129066876317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 440930630502086044584211 661395945753129066876317)
                    ·
                      refine ⟨248023479657423400078619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 661395945753129066876317 248023479657423400078619)
                      ·
                        rfl

theorem cell23_483024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 4, 1, 3].length) (baseStart_483024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483024 prefixEnd_483024 := by exact prefixLift 483024
  have htrace : WordTrace (prefixWord ++ tailWord_483024) baseStart_483024 baseEnd_483024 := by
    simpa [prefixWord, tailWord_483024, baseEnd_483024] using wordTrace_append hprefix tailTrace_483024
  have hstable : (prefixWord ++ tailWord_483024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483024).length < 2 ^ (prefixWord ++ tailWord_483024).sum := by decide
  have hdescent : baseEnd_483024 < baseStart_483024 := by decide
  rcases family_descends (prefixWord ++ tailWord_483024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483057 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 1, 8]
def baseStart_483057 : Nat := 118140960795 + 483057 * 2 ^ 59
def prefixEnd_483057 : Nat := 4983230072969 + 3 ^ 40 * 483057 * 2
def baseEnd_483057 : Nat := 82680141506340590321989

theorem tailTrace_483057 : CollatzResearch.WordTrace tailWord_483057 prefixEnd_483057 82680141506340590321989 := by
  unfold tailWord_483057
  simp only [CollatzResearch.WordTrace]
  refine ⟨17618536210974463412583425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11745690807316308941722283 17618536210974463412583425)
  ·
    refine ⟨13213902158230847559437569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17618536210974463412583425 13213902158230847559437569)
    ·
      refine ⟨9910426618673135669578177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13213902158230847559437569 9910426618673135669578177)
      ·
        refine ⟨7432819964004851752183633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9910426618673135669578177 7432819964004851752183633)
        ·
          refine ⟨5574614973003638814137725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7432819964004851752183633 5574614973003638814137725)
          ·
            refine ⟨2090480614876364555301647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5574614973003638814137725 2090480614876364555301647)
            ·
              refine ⟨3135720922314546832952471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090480614876364555301647 3135720922314546832952471)
              ·
                refine ⟨4703581383471820249428707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135720922314546832952471 4703581383471820249428707)
                ·
                  refine ⟨7055372075207730374143061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4703581383471820249428707 7055372075207730374143061)
                  ·
                    refine ⟨82680141506340590321989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7055372075207730374143061 82680141506340590321989)
                    ·
                      rfl

theorem cell23_483057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_483057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483057 prefixEnd_483057 := by exact prefixLift 483057
  have htrace : WordTrace (prefixWord ++ tailWord_483057) baseStart_483057 baseEnd_483057 := by
    simpa [prefixWord, tailWord_483057, baseEnd_483057] using wordTrace_append hprefix tailTrace_483057
  have hstable : (prefixWord ++ tailWord_483057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483057).length < 2 ^ (prefixWord ++ tailWord_483057).sum := by decide
  have hdescent : baseEnd_483057 < baseStart_483057 := by decide
  rcases family_descends (prefixWord ++ tailWord_483057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483067 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 5]
def baseStart_483067 : Nat := 118140960795 + 483067 * 2 ^ 59
def prefixEnd_483067 : Nat := 4983230072969 + 3 ^ 40 * 483067 * 2
def baseEnd_483067 : Nat := 248045559325566731840921

theorem tailTrace_483067 : CollatzResearch.WordTrace tailWord_483067 prefixEnd_483067 248045559325566731840921 := by
  unfold tailWord_483067
  simp only [CollatzResearch.WordTrace]
  refine ⟨17618900940938235120447455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11745933960625490080298303 17618900940938235120447455)
  ·
    refine ⟨26428351411407352680671183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17618900940938235120447455 26428351411407352680671183)
    ·
      refine ⟨39642527117111029021006775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26428351411407352680671183 39642527117111029021006775)
      ·
        refine ⟨59463790675666543531510163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39642527117111029021006775 59463790675666543531510163)
        ·
          refine ⟨89195686013499815297265245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59463790675666543531510163 89195686013499815297265245)
          ·
            refine ⟨33448382255062430736474467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89195686013499815297265245 33448382255062430736474467)
            ·
              refine ⟨50172573382593646104711701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33448382255062430736474467 50172573382593646104711701)
              ·
                refine ⟨2351839377309077161158361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50172573382593646104711701 2351839377309077161158361)
                ·
                  refine ⟨1763879532981807870868771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2351839377309077161158361 1763879532981807870868771)
                  ·
                    refine ⟨2645819299472711806303157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1763879532981807870868771 2645819299472711806303157)
                    ·
                      refine ⟨248045559325566731840921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2645819299472711806303157 248045559325566731840921)
                      ·
                        rfl

theorem cell23_483067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 5].length) (baseStart_483067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483067 prefixEnd_483067 := by exact prefixLift 483067
  have htrace : WordTrace (prefixWord ++ tailWord_483067) baseStart_483067 baseEnd_483067 := by
    simpa [prefixWord, tailWord_483067, baseEnd_483067] using wordTrace_append hprefix tailTrace_483067
  have hstable : (prefixWord ++ tailWord_483067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483067).length < 2 ^ (prefixWord ++ tailWord_483067).sum := by decide
  have hdescent : baseEnd_483067 < baseStart_483067 := by decide
  rcases family_descends (prefixWord ++ tailWord_483067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483074 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_483074 : Nat := 118140960795 + 483074 * 2 ^ 59
def prefixEnd_483074 : Nat := 4983230072969 + 3 ^ 40 * 483074 * 2
def baseEnd_483074 : Nat := 82683051230049401484463

theorem tailTrace_483074 : CollatzResearch.WordTrace tailWord_483074 prefixEnd_483074 82683051230049401484463 := by
  unfold tailWord_483074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4404789062978218828988069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11746104167941916877301517 4404789062978218828988069)
  ·
    refine ⟨825897949308416030435263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4404789062978218828988069 825897949308416030435263)
    ·
      refine ⟨1238846923962624045652895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 825897949308416030435263 1238846923962624045652895)
      ·
        refine ⟨1858270385943936068479343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238846923962624045652895 1858270385943936068479343)
        ·
          refine ⟨2787405578915904102719015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858270385943936068479343 2787405578915904102719015)
          ·
            refine ⟨4181108368373856154078523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787405578915904102719015 4181108368373856154078523)
            ·
              refine ⟨6271662552560784231117785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4181108368373856154078523 6271662552560784231117785)
              ·
                refine ⟨4703746914420588173338339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6271662552560784231117785 4703746914420588173338339)
                ·
                  refine ⟨7055620371630882260007509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4703746914420588173338339 7055620371630882260007509)
                  ·
                    refine ⟨82683051230049401484463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7055620371630882260007509 82683051230049401484463)
                    ·
                      rfl

theorem cell23_483074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_483074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483074 prefixEnd_483074 := by exact prefixLift 483074
  have htrace : WordTrace (prefixWord ++ tailWord_483074) baseStart_483074 baseEnd_483074 := by
    simpa [prefixWord, tailWord_483074, baseEnd_483074] using wordTrace_append hprefix tailTrace_483074
  have hstable : (prefixWord ++ tailWord_483074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483074).length < 2 ^ (prefixWord ++ tailWord_483074).sum := by decide
  have hdescent : baseEnd_483074 < baseStart_483074 := by decide
  rcases family_descends (prefixWord ++ tailWord_483074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483081 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 4, 2, 2]
def baseStart_483081 : Nat := 118140960795 + 483081 * 2 ^ 59
def prefixEnd_483081 : Nat := 4983230072969 + 3 ^ 40 * 483081 * 2
def baseEnd_483081 : Nat := 248052748054729677065857

theorem tailTrace_483081 : CollatzResearch.WordTrace tailWord_483081 prefixEnd_483081 248052748054729677065857 := by
  unfold tailWord_483081
  simp only [CollatzResearch.WordTrace]
  refine ⟨17619411562887515511457097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11746274375258343674304731 17619411562887515511457097)
  ·
    refine ⟨13214558672165636633592823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17619411562887515511457097 13214558672165636633592823)
    ·
      refine ⟨19821838008248454950389235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13214558672165636633592823 19821838008248454950389235)
      ·
        refine ⟨29732757012372682425583853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19821838008248454950389235 29732757012372682425583853)
        ·
          refine ⟨11149783879639755909593945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29732757012372682425583853 11149783879639755909593945)
          ·
            refine ⟨8362337909729816932195459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11149783879639755909593945 8362337909729816932195459)
            ·
              refine ⟨12543506864594725398293189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8362337909729816932195459 12543506864594725398293189)
              ·
                refine ⟨2351907537111511012179973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12543506864594725398293189 2351907537111511012179973)
                ·
                  refine ⟨440982663208408314783745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2351907537111511012179973 440982663208408314783745)
                  ·
                    refine ⟨330736997406306236087809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 440982663208408314783745 330736997406306236087809)
                    ·
                      refine ⟨248052748054729677065857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 330736997406306236087809 248052748054729677065857)
                      ·
                        rfl

theorem cell23_483081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 2, 2].length) (baseStart_483081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483081 prefixEnd_483081 := by exact prefixLift 483081
  have htrace : WordTrace (prefixWord ++ tailWord_483081) baseStart_483081 baseEnd_483081 := by
    simpa [prefixWord, tailWord_483081, baseEnd_483081] using wordTrace_append hprefix tailTrace_483081
  have hstable : (prefixWord ++ tailWord_483081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483081).length < 2 ^ (prefixWord ++ tailWord_483081).sum := by decide
  have hdescent : baseEnd_483081 < baseStart_483081 := by decide
  rcases family_descends (prefixWord ++ tailWord_483081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483092 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_483092 : Nat := 118140960795 + 483092 * 2 ^ 59
def prefixEnd_483092 : Nat := 4983230072969 + 3 ^ 40 * 483092 * 2
def baseEnd_483092 : Nat := 248058396341929134028307

theorem tailTrace_483092 : CollatzResearch.WordTrace tailWord_483092 prefixEnd_483092 248058396341929134028307 := by
  unfold tailWord_483092
  simp only [CollatzResearch.WordTrace]
  refine ⟨8809906382923832195053765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11746541843898442926738353 8809906382923832195053765)
  ·
    refine ⟨1651857446798218536572581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8809906382923832195053765 1651857446798218536572581)
    ·
      refine ⟨309723271274665975607359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1651857446798218536572581 309723271274665975607359)
      ·
        refine ⟨464584906911998963411039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309723271274665975607359 464584906911998963411039)
        ·
          refine ⟨696877360367998445116559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464584906911998963411039 696877360367998445116559)
          ·
            refine ⟨1045316040551997667674839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696877360367998445116559 1045316040551997667674839)
            ·
              refine ⟨1567974060827996501512259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045316040551997667674839 1567974060827996501512259)
              ·
                refine ⟨2351961091241994752268389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567974060827996501512259 2351961091241994752268389)
                ·
                  refine ⟨440992704607874016050323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2351961091241994752268389 440992704607874016050323)
                  ·
                    refine ⟨661489056911811024075485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 440992704607874016050323 661489056911811024075485)
                    ·
                      refine ⟨248058396341929134028307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 661489056911811024075485 248058396341929134028307)
                      ·
                        rfl

theorem cell23_483092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_483092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483092 prefixEnd_483092 := by exact prefixLift 483092
  have htrace : WordTrace (prefixWord ++ tailWord_483092) baseStart_483092 baseEnd_483092 := by
    simpa [prefixWord, tailWord_483092, baseEnd_483092] using wordTrace_append hprefix tailTrace_483092
  have hstable : (prefixWord ++ tailWord_483092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483092).length < 2 ^ (prefixWord ++ tailWord_483092).sum := by decide
  have hdescent : baseEnd_483092 < baseStart_483092 := by decide
  rcases family_descends (prefixWord ++ tailWord_483092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483098 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2]
def baseStart_483098 : Nat := 118140960795 + 483098 * 2 ^ 59
def prefixEnd_483098 : Nat := 4983230072969 + 3 ^ 40 * 483098 * 2
def baseEnd_483098 : Nat := 248061477225856110553279

theorem tailTrace_483098 : CollatzResearch.WordTrace tailWord_483098 prefixEnd_483098 248061477225856110553279 := by
  unfold tailWord_483098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4405007900956481853706487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11746687735883951609883965 4405007900956481853706487)
  ·
    refine ⟨6607511851434722780559731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4405007900956481853706487 6607511851434722780559731)
    ·
      refine ⟨9911267777152084170839597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6607511851434722780559731 9911267777152084170839597)
      ·
        refine ⟨3716725416432031564064849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9911267777152084170839597 3716725416432031564064849)
        ·
          refine ⟨2787544062324023673048637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3716725416432031564064849 2787544062324023673048637)
          ·
            refine ⟨1045329023371508877393239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2787544062324023673048637 1045329023371508877393239)
            ·
              refine ⟨1567993535057263316089859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045329023371508877393239 1567993535057263316089859)
              ·
                refine ⟨2351990302585894974134789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567993535057263316089859 2351990302585894974134789)
                ·
                  refine ⟨440998181734855307650273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2351990302585894974134789 440998181734855307650273)
                  ·
                    refine ⟨330748636301141480737705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 440998181734855307650273 330748636301141480737705)
                    ·
                      refine ⟨248061477225856110553279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 330748636301141480737705 248061477225856110553279)
                      ·
                        rfl

theorem cell23_483098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_483098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483098 prefixEnd_483098 := by exact prefixLift 483098
  have htrace : WordTrace (prefixWord ++ tailWord_483098) baseStart_483098 baseEnd_483098 := by
    simpa [prefixWord, tailWord_483098, baseEnd_483098] using wordTrace_append hprefix tailTrace_483098
  have hstable : (prefixWord ++ tailWord_483098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483098).length < 2 ^ (prefixWord ++ tailWord_483098).sum := by decide
  have hdescent : baseEnd_483098 < baseStart_483098 := by decide
  rcases family_descends (prefixWord ++ tailWord_483098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483104 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 7]
def baseStart_483104 : Nat := 118140960795 + 483104 * 2 ^ 59
def prefixEnd_483104 : Nat := 4983230072969 + 3 ^ 40 * 483104 * 2
def baseEnd_483104 : Nat := 27562728678864787453139

theorem tailTrace_483104 : CollatzResearch.WordTrace tailWord_483104 prefixEnd_483104 27562728678864787453139 := by
  unfold tailWord_483104
  simp only [CollatzResearch.WordTrace]
  refine ⟨8810125220902095219772183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11746833627869460293029577 8810125220902095219772183)
  ·
    refine ⟨13215187831353142829658275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8810125220902095219772183 13215187831353142829658275)
    ·
      refine ⟨19822781747029714244487413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13215187831353142829658275 19822781747029714244487413)
      ·
        refine ⟨1858385788784035710420695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19822781747029714244487413 1858385788784035710420695)
        ·
          refine ⟨2787578683176053565631043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858385788784035710420695 2787578683176053565631043)
          ·
            refine ⟨4181368024764080348446565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787578683176053565631043 4181368024764080348446565)
            ·
              refine ⟨784006504643265065333731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4181368024764080348446565 784006504643265065333731)
              ·
                refine ⟨1176009756964897598000597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784006504643265065333731 1176009756964897598000597)
                ·
                  refine ⟨27562728678864787453139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1176009756964897598000597 27562728678864787453139)
                  ·
                    rfl

theorem cell23_483104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 7].length) (baseStart_483104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483104 prefixEnd_483104 := by exact prefixLift 483104
  have htrace : WordTrace (prefixWord ++ tailWord_483104) baseStart_483104 baseEnd_483104 := by
    simpa [prefixWord, tailWord_483104, baseEnd_483104] using wordTrace_append hprefix tailTrace_483104
  have hstable : (prefixWord ++ tailWord_483104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483104).length < 2 ^ (prefixWord ++ tailWord_483104).sum := by decide
  have hdescent : baseEnd_483104 < baseStart_483104 := by decide
  rcases family_descends (prefixWord ++ tailWord_483104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483127 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_483127 : Nat := 118140960795 + 483127 * 2 ^ 59
def prefixEnd_483127 : Nat := 4983230072969 + 3 ^ 40 * 483127 * 2
def baseEnd_483127 : Nat := 248076368164836497090645

theorem tailTrace_483127 : CollatzResearch.WordTrace tailWord_483127 prefixEnd_483127 248076368164836497090645 := by
  unfold tailWord_483127
  simp only [CollatzResearch.WordTrace]
  refine ⟨17621089320720865367631635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11747392880480576911754423 17621089320720865367631635)
  ·
    refine ⟨26431633981081298051447453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17621089320720865367631635 26431633981081298051447453)
    ·
      refine ⟨9911862742905486769292795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26431633981081298051447453 9911862742905486769292795)
      ·
        refine ⟨14867794114358230153939193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9911862742905486769292795 14867794114358230153939193)
        ·
          refine ⟨11150845585768672615454395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14867794114358230153939193 11150845585768672615454395)
          ·
            refine ⟨16726268378653008923181593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11150845585768672615454395 16726268378653008923181593)
            ·
              refine ⟨12544701283989756692386195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16726268378653008923181593 12544701283989756692386195)
              ·
                refine ⟨18817051925984635038579293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12544701283989756692386195 18817051925984635038579293)
                ·
                  refine ⟨7056394472244238139467235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18817051925984635038579293 7056394472244238139467235)
                  ·
                    refine ⟨10584591708366357209200853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7056394472244238139467235 10584591708366357209200853)
                    ·
                      refine ⟨248076368164836497090645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10584591708366357209200853 248076368164836497090645)
                      ·
                        rfl

theorem cell23_483127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_483127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483127 prefixEnd_483127 := by exact prefixLift 483127
  have htrace : WordTrace (prefixWord ++ tailWord_483127) baseStart_483127 baseEnd_483127 := by
    simpa [prefixWord, tailWord_483127, baseEnd_483127] using wordTrace_append hprefix tailTrace_483127
  have hstable : (prefixWord ++ tailWord_483127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483127).length < 2 ^ (prefixWord ++ tailWord_483127).sum := by decide
  have hdescent : baseEnd_483127 < baseStart_483127 := by decide
  rcases family_descends (prefixWord ++ tailWord_483127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483181 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_483181 : Nat := 118140960795 + 483181 * 2 ^ 59
def prefixEnd_483181 : Nat := 4983230072969 + 3 ^ 40 * 483181 * 2
def baseEnd_483181 : Nat := 82701365373393095271799

theorem tailTrace_483181 : CollatzResearch.WordTrace tailWord_483181 prefixEnd_483181 82701365373393095271799 := by
  unfold tailWord_483181
  simp only [CollatzResearch.WordTrace]
  refine ⟨17623058862525232590097397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11748705908350155060064931 17623058862525232590097397)
  ·
    refine ⟨1652161768361740555321631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17623058862525232590097397 1652161768361740555321631)
    ·
      refine ⟨2478242652542610832982447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1652161768361740555321631 2478242652542610832982447)
      ·
        refine ⟨3717363978813916249473671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2478242652542610832982447 3717363978813916249473671)
        ·
          refine ⟨5576045968220874374210507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3717363978813916249473671 5576045968220874374210507)
          ·
            refine ⟨8364068952331311561315761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5576045968220874374210507 8364068952331311561315761)
            ·
              refine ⟨6273051714248483670986821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8364068952331311561315761 6273051714248483670986821)
              ·
                refine ⟨1176197196421590688310029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6273051714248483670986821 1176197196421590688310029)
                ·
                  refine ⟨441073948658096508116261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1176197196421590688310029 441073948658096508116261)
                  ·
                    refine ⟨82701365373393095271799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 441073948658096508116261 82701365373393095271799)
                    ·
                      rfl

theorem cell23_483181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_483181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483181 prefixEnd_483181 := by exact prefixLift 483181
  have htrace : WordTrace (prefixWord ++ tailWord_483181) baseStart_483181 baseEnd_483181 := by
    simpa [prefixWord, tailWord_483181, baseEnd_483181] using wordTrace_append hprefix tailTrace_483181
  have hstable : (prefixWord ++ tailWord_483181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483181).length < 2 ^ (prefixWord ++ tailWord_483181).sum := by decide
  have hdescent : baseEnd_483181 < baseStart_483181 := by decide
  rcases family_descends (prefixWord ++ tailWord_483181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483281 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 3, 2, 3]
def baseStart_483281 : Nat := 118140960795 + 483281 * 2 ^ 59
def prefixEnd_483281 : Nat := 4983230072969 + 3 ^ 40 * 483281 * 2
def baseEnd_483281 : Nat := 248155444185628894564937

theorem tailTrace_483281 : CollatzResearch.WordTrace tailWord_483281 prefixEnd_483281 248155444185628894564937 := by
  unfold tailWord_483281
  simp only [CollatzResearch.WordTrace]
  refine ⟨17626706162162949668737697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11751137441441966445825131 17626706162162949668737697)
  ·
    refine ⟨13220029621622212251553273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17626706162162949668737697 13220029621622212251553273)
    ·
      refine ⟨9915022216216659188664955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13220029621622212251553273 9915022216216659188664955)
      ·
        refine ⟨14872533324324988782997433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9915022216216659188664955 14872533324324988782997433)
        ·
          refine ⟨11154399993243741587248075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14872533324324988782997433 11154399993243741587248075)
          ·
            refine ⟨16731599989865612380872113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11154399993243741587248075 16731599989865612380872113)
            ·
              refine ⟨12548699992399209285654085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16731599989865612380872113 12548699992399209285654085)
              ·
                refine ⟨2352881248574851741060141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12548699992399209285654085 2352881248574851741060141)
                ·
                  refine ⟨882330468215569402897553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2352881248574851741060141 882330468215569402897553)
                  ·
                    refine ⟨661747851161677052173165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 882330468215569402897553 661747851161677052173165)
                    ·
                      refine ⟨248155444185628894564937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 661747851161677052173165 248155444185628894564937)
                      ·
                        rfl

theorem cell23_483281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_483281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483281 prefixEnd_483281 := by exact prefixLift 483281
  have htrace : WordTrace (prefixWord ++ tailWord_483281) baseStart_483281 baseEnd_483281 := by
    simpa [prefixWord, tailWord_483281, baseEnd_483281] using wordTrace_append hprefix tailTrace_483281
  have hstable : (prefixWord ++ tailWord_483281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483281).length < 2 ^ (prefixWord ++ tailWord_483281).sum := by decide
  have hdescent : baseEnd_483281 < baseStart_483281 := by decide
  rcases family_descends (prefixWord ++ tailWord_483281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483295 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 3, 2, 2]
def baseStart_483295 : Nat := 118140960795 + 483295 * 2 ^ 59
def prefixEnd_483295 : Nat := 4983230072969 + 3 ^ 40 * 483295 * 2
def baseEnd_483295 : Nat := 248162632914791839789873

theorem tailTrace_483295 : CollatzResearch.WordTrace tailWord_483295 prefixEnd_483295 248162632914791839789873 := by
  unfold tailWord_483295
  simp only [CollatzResearch.WordTrace]
  refine ⟨17627216784112230059747339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11751477856074820039831559 17627216784112230059747339)
  ·
    refine ⟨26440825176168345089621009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17627216784112230059747339 26440825176168345089621009)
    ·
      refine ⟨19830618882126258817215757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26440825176168345089621009 19830618882126258817215757)
      ·
        refine ⟨7436482080797347056455909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19830618882126258817215757 7436482080797347056455909)
        ·
          refine ⟨1394340390149502573085483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7436482080797347056455909 1394340390149502573085483)
          ·
            refine ⟨2091510585224253859628225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394340390149502573085483 2091510585224253859628225)
            ·
              refine ⟨1568632938918190394721169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2091510585224253859628225 1568632938918190394721169)
              ·
                refine ⟨1176474704188642796040877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1568632938918190394721169 1176474704188642796040877)
                ·
                  refine ⟨441178014070741048515329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1176474704188642796040877 441178014070741048515329)
                  ·
                    refine ⟨330883510553055786386497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 441178014070741048515329 330883510553055786386497)
                    ·
                      refine ⟨248162632914791839789873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 330883510553055786386497 248162632914791839789873)
                      ·
                        rfl

theorem cell23_483295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_483295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483295 prefixEnd_483295 := by exact prefixLift 483295
  have htrace : WordTrace (prefixWord ++ tailWord_483295) baseStart_483295 baseEnd_483295 := by
    simpa [prefixWord, tailWord_483295, baseEnd_483295] using wordTrace_append hprefix tailTrace_483295
  have hstable : (prefixWord ++ tailWord_483295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483295).length < 2 ^ (prefixWord ++ tailWord_483295).sum := by decide
  have hdescent : baseEnd_483295 < baseStart_483295 := by decide
  rcases family_descends (prefixWord ++ tailWord_483295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483311 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 3]
def baseStart_483311 : Nat := 118140960795 + 483311 * 2 ^ 59
def prefixEnd_483311 : Nat := 4983230072969 + 3 ^ 40 * 483311 * 2
def baseEnd_483311 : Nat := 248170848605263777189799

theorem tailTrace_483311 : CollatzResearch.WordTrace tailWord_483311 prefixEnd_483311 248170848605263777189799 := by
  unfold tailWord_483311
  simp only [CollatzResearch.WordTrace]
  refine ⟨17627800352054264792329787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11751866901369509861553191 17627800352054264792329787)
  ·
    refine ⟨26441700528081397188494681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17627800352054264792329787 26441700528081397188494681)
    ·
      refine ⟨19831275396061047891371011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26441700528081397188494681 19831275396061047891371011)
      ·
        refine ⟨29746913094091571837056517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19831275396061047891371011 29746913094091571837056517)
        ·
          refine ⟨5577546205142169719448097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29746913094091571837056517 5577546205142169719448097)
          ·
            refine ⟨4183159653856627289586073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5577546205142169719448097 4183159653856627289586073)
            ·
              refine ⟨3137369740392470467189555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4183159653856627289586073 3137369740392470467189555)
              ·
                refine ⟨4706054610588705700784333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137369740392470467189555 4706054610588705700784333)
                ·
                  refine ⟨1764770478970764637794125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4706054610588705700784333 1764770478970764637794125)
                  ·
                    refine ⟨661788929614036739172797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1764770478970764637794125 661788929614036739172797)
                    ·
                      refine ⟨248170848605263777189799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 661788929614036739172797 248170848605263777189799)
                      ·
                        rfl

theorem cell23_483311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 3].length) (baseStart_483311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483311 prefixEnd_483311 := by exact prefixLift 483311
  have htrace : WordTrace (prefixWord ++ tailWord_483311) baseStart_483311 baseEnd_483311 := by
    simpa [prefixWord, tailWord_483311, baseEnd_483311] using wordTrace_append hprefix tailTrace_483311
  have hstable : (prefixWord ++ tailWord_483311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483311).length < 2 ^ (prefixWord ++ tailWord_483311).sum := by decide
  have hdescent : baseEnd_483311 < baseStart_483311 := by decide
  rcases family_descends (prefixWord ++ tailWord_483311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483312 : List Nat := [2, 1, 1, 1, 3, 2, 5, 3, 1, 2, 2]
def baseStart_483312 : Nat := 118140960795 + 483312 * 2 ^ 59
def prefixEnd_483312 : Nat := 4983230072969 + 3 ^ 40 * 483312 * 2
def baseEnd_483312 : Nat := 248171362085918273277295

theorem tailTrace_483312 : CollatzResearch.WordTrace tailWord_483312 prefixEnd_483312 248171362085918273277295 := by
  unfold tailWord_483312
  simp only [CollatzResearch.WordTrace]
  refine ⟨8813918412525320981558095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11751891216700427975410793 8813918412525320981558095)
  ·
    refine ⟨13220877618787981472337143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8813918412525320981558095 13220877618787981472337143)
    ·
      refine ⟨19831316428181972208505715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13220877618787981472337143 19831316428181972208505715)
      ·
        refine ⟨29746974642272958312758573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19831316428181972208505715 29746974642272958312758573)
        ·
          refine ⟨11155115490852359367284465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29746974642272958312758573 11155115490852359367284465)
          ·
            refine ⟨8366336618139269525463349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11155115490852359367284465 8366336618139269525463349)
            ·
              refine ⟨784344057950556518012189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8366336618139269525463349 784344057950556518012189)
              ·
                refine ⟨294129021731458694254571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 784344057950556518012189 294129021731458694254571)
                ·
                  refine ⟨441193532597188041381857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294129021731458694254571 441193532597188041381857)
                  ·
                    refine ⟨330895149447891031036393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 441193532597188041381857 330895149447891031036393)
                    ·
                      refine ⟨248171362085918273277295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 330895149447891031036393 248171362085918273277295)
                      ·
                        rfl

theorem cell23_483312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 1, 2, 2].length) (baseStart_483312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483312 prefixEnd_483312 := by exact prefixLift 483312
  have htrace : WordTrace (prefixWord ++ tailWord_483312) baseStart_483312 baseEnd_483312 := by
    simpa [prefixWord, tailWord_483312, baseEnd_483312] using wordTrace_append hprefix tailTrace_483312
  have hstable : (prefixWord ++ tailWord_483312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483312).length < 2 ^ (prefixWord ++ tailWord_483312).sum := by decide
  have hdescent : baseEnd_483312 < baseStart_483312 := by decide
  rcases family_descends (prefixWord ++ tailWord_483312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483318 : List Nat := [5, 1, 1, 1, 4, 2, 9]
def baseStart_483318 : Nat := 118140960795 + 483318 * 2 ^ 59
def prefixEnd_483318 : Nat := 4983230072969 + 3 ^ 40 * 483318 * 2
def baseEnd_483318 : Nat := 3063882011973398145707

theorem tailTrace_483318 : CollatzResearch.WordTrace tailWord_483318 prefixEnd_483318 3063882011973398145707 := by
  unfold tailWord_483318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1101753478939306561739663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11752037108685936658556405 1101753478939306561739663)
  ·
    refine ⟨1652630218408959842609495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1101753478939306561739663 1652630218408959842609495)
    ·
      refine ⟨2478945327613439763914243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1652630218408959842609495 2478945327613439763914243)
      ·
        refine ⟨3718417991420159645871365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2478945327613439763914243 3718417991420159645871365)
        ·
          refine ⟨697203373391279933600881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3718417991420159645871365 697203373391279933600881)
          ·
            refine ⟨522902530043459950200661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697203373391279933600881 522902530043459950200661)
            ·
              refine ⟨3063882011973398145707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 522902530043459950200661 3063882011973398145707)
              ·
                rfl

theorem cell23_483318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 9].length) (baseStart_483318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483318 prefixEnd_483318 := by exact prefixLift 483318
  have htrace : WordTrace (prefixWord ++ tailWord_483318) baseStart_483318 baseEnd_483318 := by
    simpa [prefixWord, tailWord_483318, baseEnd_483318] using wordTrace_append hprefix tailTrace_483318
  have hstable : (prefixWord ++ tailWord_483318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483318).length < 2 ^ (prefixWord ++ tailWord_483318).sum := by decide
  have hdescent : baseEnd_483318 < baseStart_483318 := by decide
  rcases family_descends (prefixWord ++ tailWord_483318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483329 : List Nat := [1, 2, 4, 1, 2, 1, 5, 2, 1, 2, 2]
def baseStart_483329 : Nat := 118140960795 + 483329 * 2 ^ 59
def prefixEnd_483329 : Nat := 4983230072969 + 3 ^ 40 * 483329 * 2
def baseEnd_483329 : Nat := 248180091257044706764717

theorem tailTrace_483329 : CollatzResearch.WordTrace tailWord_483329 prefixEnd_483329 248180091257044706764717 := by
  unfold tailWord_483329
  simp only [CollatzResearch.WordTrace]
  refine ⟨17628456865989053866485041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11752304577326035910990027 17628456865989053866485041)
  ·
    refine ⟨13221342649491790399863781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17628456865989053866485041 13221342649491790399863781)
    ·
      refine ⟨2479001746779710699974459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13221342649491790399863781 2479001746779710699974459)
      ·
        refine ⟨3718502620169566049961689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2479001746779710699974459 3718502620169566049961689)
        ·
          refine ⟨2788876965127174537471267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3718502620169566049961689 2788876965127174537471267)
          ·
            refine ⟨4183315447690761806206901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788876965127174537471267 4183315447690761806206901)
            ·
              refine ⟨392185823221008919331897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4183315447690761806206901 392185823221008919331897)
              ·
                refine ⟨294139367415756689498923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392185823221008919331897 294139367415756689498923)
                ·
                  refine ⟨441209051123635034248385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294139367415756689498923 441209051123635034248385)
                  ·
                    refine ⟨330906788342726275686289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 441209051123635034248385 330906788342726275686289)
                    ·
                      refine ⟨248180091257044706764717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 330906788342726275686289 248180091257044706764717)
                      ·
                        rfl

theorem cell23_483329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_483329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483329 prefixEnd_483329 := by exact prefixLift 483329
  have htrace : WordTrace (prefixWord ++ tailWord_483329) baseStart_483329 baseEnd_483329 := by
    simpa [prefixWord, tailWord_483329, baseEnd_483329] using wordTrace_append hprefix tailTrace_483329
  have hstable : (prefixWord ++ tailWord_483329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483329).length < 2 ^ (prefixWord ++ tailWord_483329).sum := by decide
  have hdescent : baseEnd_483329 < baseStart_483329 := by decide
  rcases family_descends (prefixWord ++ tailWord_483329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483380 : List Nat := [2, 5, 1, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_483380 : Nat := 118140960795 + 483380 * 2 ^ 59
def prefixEnd_483380 : Nat := 4983230072969 + 3 ^ 40 * 483380 * 2
def baseEnd_483380 : Nat := 248206278770424007226983

theorem tailTrace_483380 : CollatzResearch.WordTrace tailWord_483380 prefixEnd_483380 248206278770424007226983 := by
  unfold tailWord_483380
  simp only [CollatzResearch.WordTrace]
  refine ⟨8815158494402144788295797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11753544659202859717727729 8815158494402144788295797)
  ·
    refine ⟨826421108850201073902731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8815158494402144788295797 826421108850201073902731)
    ·
      refine ⟨1239631663275301610854097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 826421108850201073902731 1239631663275301610854097)
      ·
        refine ⟨929723747456476208140573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1239631663275301610854097 929723747456476208140573)
        ·
          refine ⟨348646405296178578052715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 929723747456476208140573 348646405296178578052715)
          ·
            refine ⟨522969607944267867079073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348646405296178578052715 522969607944267867079073)
            ·
              refine ⟨392227205958200900309305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522969607944267867079073 392227205958200900309305)
              ·
                refine ⟨294170404468650675231979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392227205958200900309305 294170404468650675231979)
                ·
                  refine ⟨441255606702976012847969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294170404468650675231979 441255606702976012847969)
                  ·
                    refine ⟨330941705027232009635977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 441255606702976012847969 330941705027232009635977)
                    ·
                      refine ⟨248206278770424007226983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 330941705027232009635977 248206278770424007226983)
                      ·
                        rfl

theorem cell23_483380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_483380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483380 prefixEnd_483380 := by exact prefixLift 483380
  have htrace : WordTrace (prefixWord ++ tailWord_483380) baseStart_483380 baseEnd_483380 := by
    simpa [prefixWord, tailWord_483380, baseEnd_483380] using wordTrace_append hprefix tailTrace_483380
  have hstable : (prefixWord ++ tailWord_483380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483380).length < 2 ^ (prefixWord ++ tailWord_483380).sum := by decide
  have hdescent : baseEnd_483380 < baseStart_483380 := by decide
  rcases family_descends (prefixWord ++ tailWord_483380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483438 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_483438 : Nat := 118140960795 + 483438 * 2 ^ 59
def prefixEnd_483438 : Nat := 4983230072969 + 3 ^ 40 * 483438 * 2
def baseEnd_483438 : Nat := 82745353549461593433905

theorem tailTrace_483438 : CollatzResearch.WordTrace tailWord_483438 prefixEnd_483438 82745353549461593433905 := by
  unfold tailWord_483438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2204054052824270685275371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11754954948396110321468645 2204054052824270685275371)
  ·
    refine ⟨3306081079236406027913057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2204054052824270685275371 3306081079236406027913057)
    ·
      refine ⟨2479560809427304520934793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3306081079236406027913057 2479560809427304520934793)
      ·
        refine ⟨1859670607070478390701095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2479560809427304520934793 1859670607070478390701095)
        ·
          refine ⟨2789505910605717586051643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1859670607070478390701095 2789505910605717586051643)
          ·
            refine ⟨4184258865908576379077465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789505910605717586051643 4184258865908576379077465)
            ·
              refine ⟨3138194149431432284308099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4184258865908576379077465 3138194149431432284308099)
              ·
                refine ⟨4707291224147148426462149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3138194149431432284308099 4707291224147148426462149)
                ·
                  refine ⟨882617104527590329961653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4707291224147148426462149 882617104527590329961653)
                  ·
                    refine ⟨82745353549461593433905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 882617104527590329961653 82745353549461593433905)
                    ·
                      rfl

theorem cell23_483438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_483438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483438 prefixEnd_483438 := by exact prefixLift 483438
  have htrace : WordTrace (prefixWord ++ tailWord_483438) baseStart_483438 baseEnd_483438 := by
    simpa [prefixWord, tailWord_483438, baseEnd_483438] using wordTrace_append hprefix tailTrace_483438
  have hstable : (prefixWord ++ tailWord_483438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483438).length < 2 ^ (prefixWord ++ tailWord_483438).sum := by decide
  have hdescent : baseEnd_483438 < baseStart_483438 := by decide
  rcases family_descends (prefixWord ++ tailWord_483438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483476 : List Nat := [2, 4, 2, 3, 2, 1, 1, 3, 5]
def baseStart_483476 : Nat := 118140960795 + 483476 * 2 ^ 59
def prefixEnd_483476 : Nat := 4983230072969 + 3 ^ 40 * 483476 * 2
def baseEnd_483476 : Nat := 27583952545917292402949

theorem tailTrace_483476 : CollatzResearch.WordTrace tailWord_483476 prefixEnd_483476 27583952545917292402949 := by
  unfold tailWord_483476
  simp only [CollatzResearch.WordTrace]
  refine ⟨8816909198228248986043141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11755878930970998648057521 8816909198228248986043141)
  ·
    refine ⟨1653170474667796684883089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8816909198228248986043141 1653170474667796684883089)
    ·
      refine ⟨1239877856000847513662317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1653170474667796684883089 1239877856000847513662317)
      ·
        refine ⟨464954196000317817623369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1239877856000847513662317 464954196000317817623369)
        ·
          refine ⟨348715647000238363217527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464954196000317817623369 348715647000238363217527)
          ·
            refine ⟨523073470500357544826291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348715647000238363217527 523073470500357544826291)
            ·
              refine ⟨784610205750536317239437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523073470500357544826291 784610205750536317239437)
              ·
                refine ⟨294228827156451118964789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 784610205750536317239437 294228827156451118964789)
                ·
                  refine ⟨27583952545917292402949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 294228827156451118964789 27583952545917292402949)
                  ·
                    rfl

theorem cell23_483476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_483476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483476 prefixEnd_483476 := by exact prefixLift 483476
  have htrace : WordTrace (prefixWord ++ tailWord_483476) baseStart_483476 baseEnd_483476 := by
    simpa [prefixWord, tailWord_483476, baseEnd_483476] using wordTrace_append hprefix tailTrace_483476
  have hstable : (prefixWord ++ tailWord_483476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483476).length < 2 ^ (prefixWord ++ tailWord_483476).sum := by decide
  have hdescent : baseEnd_483476 < baseStart_483476 := by decide
  rcases family_descends (prefixWord ++ tailWord_483476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483525 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 3, 1, 3]
def baseStart_483525 : Nat := 118140960795 + 483525 * 2 ^ 59
def prefixEnd_483525 : Nat := 4983230072969 + 3 ^ 40 * 483525 * 2
def baseEnd_483525 : Nat := 248280733465325939913815

theorem tailTrace_483525 : CollatzResearch.WordTrace tailWord_483525 prefixEnd_483525 248280733465325939913815 := by
  unfold tailWord_483525
  simp only [CollatzResearch.WordTrace]
  refine ⟨17635605573278979340620029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11757070382185986227080019 17635605573278979340620029)
  ·
    refine ⟨6613352089979617252732511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17635605573278979340620029 6613352089979617252732511)
    ·
      refine ⟨9920028134969425879098767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6613352089979617252732511 9920028134969425879098767)
      ·
        refine ⟨14880042202454138818648151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9920028134969425879098767 14880042202454138818648151)
        ·
          refine ⟨22320063303681208227972227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14880042202454138818648151 22320063303681208227972227)
          ·
            refine ⟨33480094955521812341958341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22320063303681208227972227 33480094955521812341958341)
            ·
              refine ⟨6277517804160339814117189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33480094955521812341958341 6277517804160339814117189)
              ·
                refine ⟨1177034588280063715146973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6277517804160339814117189 1177034588280063715146973)
                ·
                  refine ⟨441387970605023893180115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177034588280063715146973 441387970605023893180115)
                  ·
                    refine ⟨662081955907535839770173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 441387970605023893180115 662081955907535839770173)
                    ·
                      refine ⟨248280733465325939913815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 662081955907535839770173 248280733465325939913815)
                      ·
                        rfl

theorem cell23_483525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_483525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483525 prefixEnd_483525 := by exact prefixLift 483525
  have htrace : WordTrace (prefixWord ++ tailWord_483525) baseStart_483525 baseEnd_483525 := by
    simpa [prefixWord, tailWord_483525, baseEnd_483525] using wordTrace_append hprefix tailTrace_483525
  have hstable : (prefixWord ++ tailWord_483525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483525).length < 2 ^ (prefixWord ++ tailWord_483525).sum := by decide
  have hdescent : baseEnd_483525 < baseStart_483525 := by decide
  rcases family_descends (prefixWord ++ tailWord_483525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483568 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 5]
def baseStart_483568 : Nat := 118140960795 + 483568 * 2 ^ 59
def prefixEnd_483568 : Nat := 4983230072969 + 3 ^ 40 * 483568 * 2
def baseEnd_483568 : Nat := 248302813133469271676117

theorem tailTrace_483568 : CollatzResearch.WordTrace tailWord_483568 prefixEnd_483568 248302813133469271676117 := by
  unfold tailWord_483568
  simp only [CollatzResearch.WordTrace]
  refine ⟨8818586956061598842217679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11758115941415465122956905 8818586956061598842217679)
  ·
    refine ⟨13227880434092398263326519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8818586956061598842217679 13227880434092398263326519)
    ·
      refine ⟨19841820651138597394989779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13227880434092398263326519 19841820651138597394989779)
      ·
        refine ⟨29762730976707896092484669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19841820651138597394989779 29762730976707896092484669)
        ·
          refine ⟨11161024116265461034681751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29762730976707896092484669 11161024116265461034681751)
          ·
            refine ⟨16741536174398191552022627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11161024116265461034681751 16741536174398191552022627)
            ·
              refine ⟨25112304261597287328033941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16741536174398191552022627 25112304261597287328033941)
              ·
                refine ⟨1177139262262372843501591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25112304261597287328033941 1177139262262372843501591)
                ·
                  refine ⟨1765708893393559265252387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1177139262262372843501591 1765708893393559265252387)
                  ·
                    refine ⟨2648563340090338897878581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1765708893393559265252387 2648563340090338897878581)
                    ·
                      refine ⟨248302813133469271676117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2648563340090338897878581 248302813133469271676117)
                      ·
                        rfl

theorem cell23_483568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_483568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483568 prefixEnd_483568 := by exact prefixLift 483568
  have htrace : WordTrace (prefixWord ++ tailWord_483568) baseStart_483568 baseEnd_483568 := by
    simpa [prefixWord, tailWord_483568, baseEnd_483568] using wordTrace_append hprefix tailTrace_483568
  have hstable : (prefixWord ++ tailWord_483568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483568).length < 2 ^ (prefixWord ++ tailWord_483568).sum := by decide
  have hdescent : baseEnd_483568 < baseStart_483568 := by decide
  rcases family_descends (prefixWord ++ tailWord_483568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483582 : List Nat := [4, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_483582 : Nat := 118140960795 + 483582 * 2 ^ 59
def prefixEnd_483582 : Nat := 4983230072969 + 3 ^ 40 * 483582 * 2
def baseEnd_483582 : Nat := 248310001862632216901053

theorem tailTrace_483582 : CollatzResearch.WordTrace tailWord_483582 prefixEnd_483582 248310001862632216901053 := by
  unfold tailWord_483582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2204710566759059759430625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11758456356048318716963333 2204710566759059759430625)
  ·
    refine ⟨1653532925069294819572969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2204710566759059759430625 1653532925069294819572969)
    ·
      refine ⟨1240149693801971114679727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1653532925069294819572969 1240149693801971114679727)
      ·
        refine ⟨1860224540702956672019591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240149693801971114679727 1860224540702956672019591)
        ·
          refine ⟨2790336811054435008029387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1860224540702956672019591 2790336811054435008029387)
          ·
            refine ⟨4185505216581652512044081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2790336811054435008029387 4185505216581652512044081)
            ·
              refine ⟨3139128912436239384033061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4185505216581652512044081 3139128912436239384033061)
              ·
                refine ⟨588586671081794884506199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3139128912436239384033061 588586671081794884506199)
                ·
                  refine ⟨882880006622692326759299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588586671081794884506199 882880006622692326759299)
                  ·
                    refine ⟨1324320009934038490138949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 882880006622692326759299 1324320009934038490138949)
                    ·
                      refine ⟨248310001862632216901053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1324320009934038490138949 248310001862632216901053)
                      ·
                        rfl

theorem cell23_483582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_483582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483582 prefixEnd_483582 := by exact prefixLift 483582
  have htrace : WordTrace (prefixWord ++ tailWord_483582) baseStart_483582 baseEnd_483582 := by
    simpa [prefixWord, tailWord_483582, baseEnd_483582] using wordTrace_append hprefix tailTrace_483582
  have hstable : (prefixWord ++ tailWord_483582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483582).length < 2 ^ (prefixWord ++ tailWord_483582).sum := by decide
  have hdescent : baseEnd_483582 < baseStart_483582 := by decide
  rcases family_descends (prefixWord ++ tailWord_483582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483585 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_483585 : Nat := 118140960795 + 483585 * 2 ^ 59
def prefixEnd_483585 : Nat := 4983230072969 + 3 ^ 40 * 483585 * 2
def baseEnd_483585 : Nat := 248311542304595705163539

theorem tailTrace_483585 : CollatzResearch.WordTrace tailWord_483585 prefixEnd_483585 248311542304595705163539 := by
  unfold tailWord_483585
  simp only [CollatzResearch.WordTrace]
  refine ⟨17637793953061609587804209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11758529302041073058536139 17637793953061609587804209)
  ·
    refine ⟨13228345464796207190853157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17637793953061609587804209 13228345464796207190853157)
    ·
      refine ⟨2480314774649288848284967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13228345464796207190853157 2480314774649288848284967)
      ·
        refine ⟨3720472161973933272427451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480314774649288848284967 3720472161973933272427451)
        ·
          refine ⟨5580708242960899908641177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720472161973933272427451 5580708242960899908641177)
          ·
            refine ⟨4185531182220674931480883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5580708242960899908641177 4185531182220674931480883)
            ·
              refine ⟨6278296773331012397221325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4185531182220674931480883 6278296773331012397221325)
              ·
                refine ⟨2354361289999129648957997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6278296773331012397221325 2354361289999129648957997)
                ·
                  refine ⟨882885483749673618359249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2354361289999129648957997 882885483749673618359249)
                  ·
                    refine ⟨662164112812255213769437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 882885483749673618359249 662164112812255213769437)
                    ·
                      refine ⟨248311542304595705163539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 662164112812255213769437 248311542304595705163539)
                      ·
                        rfl

theorem cell23_483585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_483585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483585 prefixEnd_483585 := by exact prefixLift 483585
  have htrace : WordTrace (prefixWord ++ tailWord_483585) baseStart_483585 baseEnd_483585 := by
    simpa [prefixWord, tailWord_483585, baseEnd_483585] using wordTrace_append hprefix tailTrace_483585
  have hstable : (prefixWord ++ tailWord_483585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483585).length < 2 ^ (prefixWord ++ tailWord_483585).sum := by decide
  have hdescent : baseEnd_483585 < baseStart_483585 := by decide
  rcases family_descends (prefixWord ++ tailWord_483585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483586 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_483586 : Nat := 118140960795 + 483586 * 2 ^ 59
def prefixEnd_483586 : Nat := 4983230072969 + 3 ^ 40 * 483586 * 2
def baseEnd_483586 : Nat := 248312055785250201251035

theorem tailTrace_483586 : CollatzResearch.WordTrace tailWord_483586 prefixEnd_483586 248312055785250201251035 := by
  unfold tailWord_483586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4409457606514496689647653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11758553617371991172393741 4409457606514496689647653)
  ·
    refine ⟨826773301221468129308935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4409457606514496689647653 826773301221468129308935)
    ·
      refine ⟨1240159951832202193963403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 826773301221468129308935 1240159951832202193963403)
      ·
        refine ⟨1860239927748303290945105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240159951832202193963403 1860239927748303290945105)
        ·
          refine ⟨1395179945811227468208829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1860239927748303290945105 1395179945811227468208829)
          ·
            refine ⟨523192479679210300578311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1395179945811227468208829 523192479679210300578311)
            ·
              refine ⟨784788719518815450867467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523192479679210300578311 784788719518815450867467)
              ·
                refine ⟨1177183079278223176301201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784788719518815450867467 1177183079278223176301201)
                ·
                  refine ⟨882887309458667382225901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1177183079278223176301201 882887309458667382225901)
                  ·
                    refine ⟨331082741047000268334713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 882887309458667382225901 331082741047000268334713)
                    ·
                      refine ⟨248312055785250201251035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 331082741047000268334713 248312055785250201251035)
                      ·
                        rfl

theorem cell23_483586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_483586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483586 prefixEnd_483586 := by exact prefixLift 483586
  have htrace : WordTrace (prefixWord ++ tailWord_483586) baseStart_483586 baseEnd_483586 := by
    simpa [prefixWord, tailWord_483586, baseEnd_483586] using wordTrace_append hprefix tailTrace_483586
  have hstable : (prefixWord ++ tailWord_483586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483586).length < 2 ^ (prefixWord ++ tailWord_483586).sum := by decide
  have hdescent : baseEnd_483586 < baseStart_483586 := by decide
  rcases family_descends (prefixWord ++ tailWord_483586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483616 : List Nat := [2, 1, 1, 5, 2, 1, 2, 4, 1, 2, 2]
def baseStart_483616 : Nat := 118140960795 + 483616 * 2 ^ 59
def prefixEnd_483616 : Nat := 4983230072969 + 3 ^ 40 * 483616 * 2
def baseEnd_483616 : Nat := 248327460204885083875897

theorem tailTrace_483616 : CollatzResearch.WordTrace tailWord_483616 prefixEnd_483616 248327460204885083875897 := by
  unfold tailWord_483616
  simp only [CollatzResearch.WordTrace]
  refine ⟨8819462307974650941091351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11759283077299534588121801 8819462307974650941091351)
  ·
    refine ⟨13229193461961976411637027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8819462307974650941091351 13229193461961976411637027)
    ·
      refine ⟨19843790192942964617455541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13229193461961976411637027 19843790192942964617455541)
      ·
        refine ⟨1860355330588402932886457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19843790192942964617455541 1860355330588402932886457)
        ·
          refine ⟨1395266497941302199664843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1860355330588402932886457 1395266497941302199664843)
          ·
            refine ⟨2092899746911953299497265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395266497941302199664843 2092899746911953299497265)
            ·
              refine ⟨1569674810183964974622949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2092899746911953299497265 1569674810183964974622949)
              ·
                refine ⟨294314026909493432741803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1569674810183964974622949 294314026909493432741803)
                ·
                  refine ⟨441471040364240149112705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294314026909493432741803 441471040364240149112705)
                  ·
                    refine ⟨331103280273180111834529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 441471040364240149112705 331103280273180111834529)
                    ·
                      refine ⟨248327460204885083875897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 331103280273180111834529 248327460204885083875897)
                      ·
                        rfl

theorem cell23_483616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_483616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483616 prefixEnd_483616 := by exact prefixLift 483616
  have htrace : WordTrace (prefixWord ++ tailWord_483616) baseStart_483616 baseEnd_483616 := by
    simpa [prefixWord, tailWord_483616, baseEnd_483616] using wordTrace_append hprefix tailTrace_483616
  have hstable : (prefixWord ++ tailWord_483616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483616).length < 2 ^ (prefixWord ++ tailWord_483616).sum := by decide
  have hdescent : baseEnd_483616 < baseStart_483616 := by decide
  rcases family_descends (prefixWord ++ tailWord_483616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483626 : List Nat := [3, 1, 4, 2, 2, 1, 3, 1, 2, 4]
def baseStart_483626 : Nat := 118140960795 + 483626 * 2 ^ 59
def prefixEnd_483626 : Nat := 4983230072969 + 3 ^ 40 * 483626 * 2
def baseEnd_483626 : Nat := 82777531670476681583617

theorem tailTrace_483626 : CollatzResearch.WordTrace tailWord_483626 prefixEnd_483626 82777531670476681583617 := by
  unfold tailWord_483626
  simp only [CollatzResearch.WordTrace]
  refine ⟨4409822336478268397511683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11759526230608715726697821 4409822336478268397511683)
  ·
    refine ⟨6614733504717402596267525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4409822336478268397511683 6614733504717402596267525)
    ·
      refine ⟨1240262532134512986800161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6614733504717402596267525 1240262532134512986800161)
      ·
        refine ⟨930196899100884740100121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1240262532134512986800161 930196899100884740100121)
        ·
          refine ⟨697647674325663555075091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 930196899100884740100121 697647674325663555075091)
          ·
            refine ⟨1046471511488495332612637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697647674325663555075091 1046471511488495332612637)
            ·
              refine ⟨392426816808185749729739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1046471511488495332612637 392426816808185749729739)
              ·
                refine ⟨588640225212278624594609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392426816808185749729739 588640225212278624594609)
                ·
                  refine ⟨441480168909208968445957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588640225212278624594609 441480168909208968445957)
                  ·
                    refine ⟨82777531670476681583617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 441480168909208968445957 82777531670476681583617)
                    ·
                      rfl

theorem cell23_483626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_483626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483626 prefixEnd_483626 := by exact prefixLift 483626
  have htrace : WordTrace (prefixWord ++ tailWord_483626) baseStart_483626 baseEnd_483626 := by
    simpa [prefixWord, tailWord_483626, baseEnd_483626] using wordTrace_append hprefix tailTrace_483626
  have hstable : (prefixWord ++ tailWord_483626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483626).length < 2 ^ (prefixWord ++ tailWord_483626).sum := by decide
  have hdescent : baseEnd_483626 < baseStart_483626 := by decide
  rcases family_descends (prefixWord ++ tailWord_483626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483648 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 4, 6]
def baseStart_483648 : Nat := 118140960795 + 483648 * 2 ^ 59
def prefixEnd_483648 : Nat := 4983230072969 + 3 ^ 40 * 483648 * 2
def baseEnd_483648 : Nat := 82781297195276319558583

theorem tailTrace_483648 : CollatzResearch.WordTrace tailWord_483648 prefixEnd_483648 82781297195276319558583 := by
  unfold tailWord_483648
  simp only [CollatzResearch.WordTrace]
  refine ⟨8820045875916685673673799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11760061167888914231565065 8820045875916685673673799)
  ·
    refine ⟨13230068813875028510510699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8820045875916685673673799 13230068813875028510510699)
    ·
      refine ⟨19845103220812542765766049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13230068813875028510510699 19845103220812542765766049)
      ·
        refine ⟨14883827415609407074324537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19845103220812542765766049 14883827415609407074324537)
        ·
          refine ⟨11162870561707055305743403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14883827415609407074324537 11162870561707055305743403)
          ·
            refine ⟨16744305842560582958615105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11162870561707055305743403 16744305842560582958615105)
            ·
              refine ⟨12558229381920437218961329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16744305842560582958615105 12558229381920437218961329)
              ·
                refine ⟨9418672036440327914220997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12558229381920437218961329 9418672036440327914220997)
                ·
                  refine ⟨1766001006832561483916437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9418672036440327914220997 1766001006832561483916437)
                  ·
                    refine ⟨82781297195276319558583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1766001006832561483916437 82781297195276319558583)
                    ·
                      rfl

theorem cell23_483648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 6].length) (baseStart_483648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483648 prefixEnd_483648 := by exact prefixLift 483648
  have htrace : WordTrace (prefixWord ++ tailWord_483648) baseStart_483648 baseEnd_483648 := by
    simpa [prefixWord, tailWord_483648, baseEnd_483648] using wordTrace_append hprefix tailTrace_483648
  have hstable : (prefixWord ++ tailWord_483648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483648).length < 2 ^ (prefixWord ++ tailWord_483648).sum := by decide
  have hdescent : baseEnd_483648 < baseStart_483648 := by decide
  rcases family_descends (prefixWord ++ tailWord_483648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483689 : List Nat := [1, 2, 1, 1, 1, 3, 5, 3, 2, 2, 2]
def baseStart_483689 : Nat := 118140960795 + 483689 * 2 ^ 59
def prefixEnd_483689 : Nat := 4983230072969 + 3 ^ 40 * 483689 * 2
def baseEnd_483689 : Nat := 248364944292663298263061

theorem tailTrace_483689 : CollatzResearch.WordTrace tailWord_483689 prefixEnd_483689 248364944292663298263061 := by
  unfold tailWord_483689
  simp only [CollatzResearch.WordTrace]
  refine ⟨17641587144684835349590121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11761058096456556899726747 17641587144684835349590121)
  ·
    refine ⟨13231190358513626512192591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17641587144684835349590121 13231190358513626512192591)
    ·
      refine ⟨19846785537770439768288887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13231190358513626512192591 19846785537770439768288887)
      ·
        refine ⟨29770178306655659652433331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19846785537770439768288887 29770178306655659652433331)
        ·
          refine ⟨44655267459983489478649997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29770178306655659652433331 44655267459983489478649997)
          ·
            refine ⟨16745725297493808554493749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44655267459983489478649997 16745725297493808554493749)
            ·
              refine ⟨1569911746640044551983789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16745725297493808554493749 1569911746640044551983789)
              ·
                refine ⟨588716904990016706993921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1569911746640044551983789 588716904990016706993921)
                ·
                  refine ⟨441537678742512530245441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588716904990016706993921 441537678742512530245441)
                  ·
                    refine ⟨331153259056884397684081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 441537678742512530245441 331153259056884397684081)
                    ·
                      refine ⟨248364944292663298263061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 331153259056884397684081 248364944292663298263061)
                      ·
                        rfl

theorem cell23_483689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 2, 2].length) (baseStart_483689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483689 prefixEnd_483689 := by exact prefixLift 483689
  have htrace : WordTrace (prefixWord ++ tailWord_483689) baseStart_483689 baseEnd_483689 := by
    simpa [prefixWord, tailWord_483689, baseEnd_483689] using wordTrace_append hprefix tailTrace_483689
  have hstable : (prefixWord ++ tailWord_483689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483689).length < 2 ^ (prefixWord ++ tailWord_483689).sum := by decide
  have hdescent : baseEnd_483689 < baseStart_483689 := by decide
  rcases family_descends (prefixWord ++ tailWord_483689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483705 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 4, 3, 3]
def baseStart_483705 : Nat := 118140960795 + 483705 * 2 ^ 59
def prefixEnd_483705 : Nat := 4983230072969 + 3 ^ 40 * 483705 * 2
def baseEnd_483705 : Nat := 248373159983135235662987

theorem tailTrace_483705 : CollatzResearch.WordTrace tailWord_483705 prefixEnd_483705 248373159983135235662987 := by
  unfold tailWord_483705
  simp only [CollatzResearch.WordTrace]
  refine ⟨17642170712626870082172569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11761447141751246721448379 17642170712626870082172569)
  ·
    refine ⟨13231628034470152561629427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17642170712626870082172569 13231628034470152561629427)
    ·
      refine ⟨19847442051705228842444141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13231628034470152561629427 19847442051705228842444141)
      ·
        refine ⟨7442790769389460815916553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19847442051705228842444141 7442790769389460815916553)
        ·
          refine ⟨5582093077042095611937415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7442790769389460815916553 5582093077042095611937415)
          ·
            refine ⟨8373139615563143417906123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5582093077042095611937415 8373139615563143417906123)
            ·
              refine ⟨12559709423344715126859185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8373139615563143417906123 12559709423344715126859185)
              ·
                refine ⟨9419782067508536345144389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12559709423344715126859185 9419782067508536345144389)
                ·
                  refine ⟨1766209137657850564714573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9419782067508536345144389 1766209137657850564714573)
                  ·
                    refine ⟨662328426621693961767965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1766209137657850564714573 662328426621693961767965)
                    ·
                      refine ⟨248373159983135235662987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 662328426621693961767965 248373159983135235662987)
                      ·
                        rfl

theorem cell23_483705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_483705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483705 prefixEnd_483705 := by exact prefixLift 483705
  have htrace : WordTrace (prefixWord ++ tailWord_483705) baseStart_483705 baseEnd_483705 := by
    simpa [prefixWord, tailWord_483705, baseEnd_483705] using wordTrace_append hprefix tailTrace_483705
  have hstable : (prefixWord ++ tailWord_483705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483705).length < 2 ^ (prefixWord ++ tailWord_483705).sum := by decide
  have hdescent : baseEnd_483705 < baseStart_483705 := by decide
  rcases family_descends (prefixWord ++ tailWord_483705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483735 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_483735 : Nat := 118140960795 + 483735 * 2 ^ 59
def prefixEnd_483735 : Nat := 4983230072969 + 3 ^ 40 * 483735 * 2
def baseEnd_483735 : Nat := 248388564402770118287849

theorem tailTrace_483735 : CollatzResearch.WordTrace tailWord_483735 prefixEnd_483735 248388564402770118287849 := by
  unfold tailWord_483735
  simp only [CollatzResearch.WordTrace]
  refine ⟨17643264902518185205764659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11762176601678790137176439 17643264902518185205764659)
  ·
    refine ⟨26464897353777277808646989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17643264902518185205764659 26464897353777277808646989)
    ·
      refine ⟨9924336507666479178242621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26464897353777277808646989 9924336507666479178242621)
      ·
        refine ⟨3721626190374929691840983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9924336507666479178242621 3721626190374929691840983)
        ·
          refine ⟨5582439285562394537761475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3721626190374929691840983 5582439285562394537761475)
          ·
            refine ⟨8373658928343591806642213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5582439285562394537761475 8373658928343591806642213)
            ·
              refine ⟨1570061049064423463745415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8373658928343591806642213 1570061049064423463745415)
              ·
                refine ⟨2355091573596635195618123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570061049064423463745415 2355091573596635195618123)
                ·
                  refine ⟨3532637360394952793427185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355091573596635195618123 3532637360394952793427185)
                  ·
                    refine ⟨2649478020296214595070389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3532637360394952793427185 2649478020296214595070389)
                    ·
                      refine ⟨248388564402770118287849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2649478020296214595070389 248388564402770118287849)
                      ·
                        rfl

theorem cell23_483735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_483735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483735 prefixEnd_483735 := by exact prefixLift 483735
  have htrace : WordTrace (prefixWord ++ tailWord_483735) baseStart_483735 baseEnd_483735 := by
    simpa [prefixWord, tailWord_483735, baseEnd_483735] using wordTrace_append hprefix tailTrace_483735
  have hstable : (prefixWord ++ tailWord_483735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483735).length < 2 ^ (prefixWord ++ tailWord_483735).sum := by decide
  have hdescent : baseEnd_483735 < baseStart_483735 := by decide
  rcases family_descends (prefixWord ++ tailWord_483735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483762 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2]
def baseStart_483762 : Nat := 118140960795 + 483762 * 2 ^ 59
def prefixEnd_483762 : Nat := 4983230072969 + 3 ^ 40 * 483762 * 2
def baseEnd_483762 : Nat := 248402428380441512650225

theorem tailTrace_483762 : CollatzResearch.WordTrace tailWord_483762 prefixEnd_483762 248402428380441512650225 := by
  unfold tailWord_483762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4411062418355092204249385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11762833115613579211331693 4411062418355092204249385)
  ·
    refine ⟨3308296813766319153187039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4411062418355092204249385 3308296813766319153187039)
    ·
      refine ⟨4962445220649478729780559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3308296813766319153187039 4962445220649478729780559)
      ·
        refine ⟨7443667830974218094670839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4962445220649478729780559 7443667830974218094670839)
        ·
          refine ⟨11165501746461327142006259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7443667830974218094670839 11165501746461327142006259)
          ·
            refine ⟨16748252619691990713009389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11165501746461327142006259 16748252619691990713009389)
            ·
              refine ⟨6280594732384496517378521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16748252619691990713009389 6280594732384496517378521)
              ·
                refine ⟨4710446049288372388033891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6280594732384496517378521 4710446049288372388033891)
                ·
                  refine ⟨7065669073932558582050837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710446049288372388033891 7065669073932558582050837)
                  ·
                    refine ⟨331203237840588683533633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7065669073932558582050837 331203237840588683533633)
                    ·
                      refine ⟨248402428380441512650225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 331203237840588683533633 248402428380441512650225)
                      ·
                        rfl

theorem cell23_483762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_483762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483762 prefixEnd_483762 := by exact prefixLift 483762
  have htrace : WordTrace (prefixWord ++ tailWord_483762) baseStart_483762 baseEnd_483762 := by
    simpa [prefixWord, tailWord_483762, baseEnd_483762] using wordTrace_append hprefix tailTrace_483762
  have hstable : (prefixWord ++ tailWord_483762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483762).length < 2 ^ (prefixWord ++ tailWord_483762).sum := by decide
  have hdescent : baseEnd_483762 < baseStart_483762 := by decide
  rcases family_descends (prefixWord ++ tailWord_483762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483832 : List Nat := [2, 1, 2, 1, 1, 4, 1, 5, 1, 5]
def baseStart_483832 : Nat := 118140960795 + 483832 * 2 ^ 59
def prefixEnd_483832 : Nat := 4983230072969 + 3 ^ 40 * 483832 * 2
def baseEnd_483832 : Nat := 82812790675418746258301

theorem tailTrace_483832 : CollatzResearch.WordTrace tailWord_483832 prefixEnd_483832 82812790675418746258301 := by
  unfold tailWord_483832
  simp only [CollatzResearch.WordTrace]
  refine ⟨8823401391583385386022875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11764535188777847181363833 8823401391583385386022875)
  ·
    refine ⟨13235102087375078079034313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8823401391583385386022875 13235102087375078079034313)
    ·
      refine ⟨9926326565531308559275735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13235102087375078079034313 9926326565531308559275735)
      ·
        refine ⟨14889489848296962838913603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9926326565531308559275735 14889489848296962838913603)
        ·
          refine ⟨22334234772445444258370405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14889489848296962838913603 22334234772445444258370405)
          ·
            refine ⟨4187669019833520798444451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22334234772445444258370405 4187669019833520798444451)
            ·
              refine ⟨6281503529750281197666677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187669019833520798444451 6281503529750281197666677)
              ·
                refine ⟨588890955914088862281251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6281503529750281197666677 588890955914088862281251)
                ·
                  refine ⟨883336433871133293421877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588890955914088862281251 883336433871133293421877)
                  ·
                    refine ⟨82812790675418746258301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 883336433871133293421877 82812790675418746258301)
                    ·
                      rfl

theorem cell23_483832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_483832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483832 prefixEnd_483832 := by exact prefixLift 483832
  have htrace : WordTrace (prefixWord ++ tailWord_483832) baseStart_483832 baseEnd_483832 := by
    simpa [prefixWord, tailWord_483832, baseEnd_483832] using wordTrace_append hprefix tailTrace_483832
  have hstable : (prefixWord ++ tailWord_483832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483832).length < 2 ^ (prefixWord ++ tailWord_483832).sum := by decide
  have hdescent : baseEnd_483832 < baseStart_483832 := by decide
  rcases family_descends (prefixWord ++ tailWord_483832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483839 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 2, 3, 2]
def baseStart_483839 : Nat := 118140960795 + 483839 * 2 ^ 59
def prefixEnd_483839 : Nat := 4983230072969 + 3 ^ 40 * 483839 * 2
def baseEnd_483839 : Nat := 248441966390837711387371

theorem tailTrace_483839 : CollatzResearch.WordTrace tailWord_483839 prefixEnd_483839 248441966390837711387371 := by
  unfold tailWord_483839
  simp only [CollatzResearch.WordTrace]
  refine ⟨17647058094141410967550571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11764705396094273978367047 17647058094141410967550571)
  ·
    refine ⟨26470587141212116451325857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17647058094141410967550571 26470587141212116451325857)
    ·
      refine ⟨19852940355909087338494393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26470587141212116451325857 19852940355909087338494393)
      ·
        refine ⟨14889705266931815503870795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19852940355909087338494393 14889705266931815503870795)
        ·
          refine ⟨22334557900397723255806193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14889705266931815503870795 22334557900397723255806193)
          ·
            refine ⟨16750918425298292441854645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22334557900397723255806193 16750918425298292441854645)
            ·
              refine ⟨1570398602371714916423873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16750918425298292441854645 1570398602371714916423873)
              ·
                refine ⟨1177798951778786187317905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1570398602371714916423873 1177798951778786187317905)
                ·
                  refine ⟨883349213834089640488429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1177798951778786187317905 883349213834089640488429)
                  ·
                    refine ⟨331255955187783615183161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 883349213834089640488429 331255955187783615183161)
                    ·
                      refine ⟨248441966390837711387371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 331255955187783615183161 248441966390837711387371)
                      ·
                        rfl

theorem cell23_483839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 3, 2].length) (baseStart_483839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483839 prefixEnd_483839 := by exact prefixLift 483839
  have htrace : WordTrace (prefixWord ++ tailWord_483839) baseStart_483839 baseEnd_483839 := by
    simpa [prefixWord, tailWord_483839, baseEnd_483839] using wordTrace_append hprefix tailTrace_483839
  have hstable : (prefixWord ++ tailWord_483839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483839).length < 2 ^ (prefixWord ++ tailWord_483839).sum := by decide
  have hdescent : baseEnd_483839 < baseStart_483839 := by decide
  rcases family_descends (prefixWord ++ tailWord_483839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483853 : List Nat := [1, 7, 1, 1, 1, 1, 4, 1, 6]
def baseStart_483853 : Nat := 118140960795 + 483853 * 2 ^ 59
def prefixEnd_483853 : Nat := 4983230072969 + 3 ^ 40 * 483853 * 2
def baseEnd_483853 : Nat := 27605461680000072956923

theorem tailTrace_483853 : CollatzResearch.WordTrace tailWord_483853 prefixEnd_483853 27605461680000072956923 := by
  unfold tailWord_483853
  simp only [CollatzResearch.WordTrace]
  refine ⟨17647568716090691358560213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11765045810727127572373475 17647568716090691358560213)
  ·
    refine ⟨413614891783375578716255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17647568716090691358560213 413614891783375578716255)
    ·
      refine ⟨620422337675063368074383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413614891783375578716255 620422337675063368074383)
      ·
        refine ⟨930633506512595052111575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620422337675063368074383 930633506512595052111575)
        ·
          refine ⟨1395950259768892578167363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930633506512595052111575 1395950259768892578167363)
          ·
            refine ⟨2093925389653338867251045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395950259768892578167363 2093925389653338867251045)
            ·
              refine ⟨392611010560001037609571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2093925389653338867251045 392611010560001037609571)
              ·
                refine ⟨588916515840001556414357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392611010560001037609571 588916515840001556414357)
                ·
                  refine ⟨27605461680000072956923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 588916515840001556414357 27605461680000072956923)
                  ·
                    rfl

theorem cell23_483853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_483853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483853 prefixEnd_483853 := by exact prefixLift 483853
  have htrace : WordTrace (prefixWord ++ tailWord_483853) baseStart_483853 baseEnd_483853 := by
    simpa [prefixWord, tailWord_483853, baseEnd_483853] using wordTrace_append hprefix tailTrace_483853
  have hstable : (prefixWord ++ tailWord_483853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483853).length < 2 ^ (prefixWord ++ tailWord_483853).sum := by decide
  have hdescent : baseEnd_483853 < baseStart_483853 := by decide
  rcases family_descends (prefixWord ++ tailWord_483853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483869 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_483869 : Nat := 118140960795 + 483869 * 2 ^ 59
def prefixEnd_483869 : Nat := 4983230072969 + 3 ^ 40 * 483869 * 2
def baseEnd_483869 : Nat := 248457370810472594012233

theorem tailTrace_483869 : CollatzResearch.WordTrace tailWord_483869 prefixEnd_483869 248457370810472594012233 := by
  unfold tailWord_483869
  simp only [CollatzResearch.WordTrace]
  refine ⟨17648152284032726091142661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11765434856021817394095107 17648152284032726091142661)
  ·
    refine ⟨3309028553256136142089249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17648152284032726091142661 3309028553256136142089249)
    ·
      refine ⟨2481771414942102106566937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3309028553256136142089249 2481771414942102106566937)
      ·
        refine ⟨1861328561206576579925203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2481771414942102106566937 1861328561206576579925203)
        ·
          refine ⟨2791992841809864869887805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861328561206576579925203 2791992841809864869887805)
          ·
            refine ⟨1046997315678699326207927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2791992841809864869887805 1046997315678699326207927)
            ·
              refine ⟨1570495973518048989311891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046997315678699326207927 1570495973518048989311891)
              ·
                refine ⟨2355743960277073483967837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570495973518048989311891 2355743960277073483967837)
                ·
                  refine ⟨883403985103902556487939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2355743960277073483967837 883403985103902556487939)
                  ·
                    refine ⟨1325105977655853834731909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 883403985103902556487939 1325105977655853834731909)
                    ·
                      refine ⟨248457370810472594012233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1325105977655853834731909 248457370810472594012233)
                      ·
                        rfl

theorem cell23_483869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_483869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483869 prefixEnd_483869 := by exact prefixLift 483869
  have htrace : WordTrace (prefixWord ++ tailWord_483869) baseStart_483869 baseEnd_483869 := by
    simpa [prefixWord, tailWord_483869, baseEnd_483869] using wordTrace_append hprefix tailTrace_483869
  have hstable : (prefixWord ++ tailWord_483869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483869).length < 2 ^ (prefixWord ++ tailWord_483869).sum := by decide
  have hdescent : baseEnd_483869 < baseStart_483869 := by decide
  rcases family_descends (prefixWord ++ tailWord_483869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483889 : List Nat := [1, 2, 2, 3, 1, 1, 2, 5, 1, 2, 3]
def baseStart_483889 : Nat := 118140960795 + 483889 * 2 ^ 59
def prefixEnd_483889 : Nat := 4983230072969 + 3 ^ 40 * 483889 * 2
def baseEnd_483889 : Nat := 248467640423562515762141

theorem tailTrace_483889 : CollatzResearch.WordTrace tailWord_483889 prefixEnd_483889 248467640423562515762141 := by
  unfold tailWord_483889
  simp only [CollatzResearch.WordTrace]
  refine ⟨17648881743960269506870721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11765921162640179671247147 17648881743960269506870721)
  ·
    refine ⟨13236661307970202130153041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17648881743960269506870721 13236661307970202130153041)
    ·
      refine ⟨9927495980977651597614781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13236661307970202130153041 9927495980977651597614781)
      ·
        refine ⟨3722810992866619349105543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9927495980977651597614781 3722810992866619349105543)
        ·
          refine ⟨5584216489299929023658315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3722810992866619349105543 5584216489299929023658315)
          ·
            refine ⟨8376324733949893535487473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5584216489299929023658315 8376324733949893535487473)
            ·
              refine ⟨6282243550462420151615605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8376324733949893535487473 6282243550462420151615605)
              ·
                refine ⟨588960332855851889213963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6282243550462420151615605 588960332855851889213963)
                ·
                  refine ⟨883440499283777833820945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588960332855851889213963 883440499283777833820945)
                  ·
                    refine ⟨662580374462833375365709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 883440499283777833820945 662580374462833375365709)
                    ·
                      refine ⟨248467640423562515762141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 662580374462833375365709 248467640423562515762141)
                      ·
                        rfl

theorem cell23_483889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_483889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483889 prefixEnd_483889 := by exact prefixLift 483889
  have htrace : WordTrace (prefixWord ++ tailWord_483889) baseStart_483889 baseEnd_483889 := by
    simpa [prefixWord, tailWord_483889, baseEnd_483889] using wordTrace_append hprefix tailTrace_483889
  have hstable : (prefixWord ++ tailWord_483889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483889).length < 2 ^ (prefixWord ++ tailWord_483889).sum := by decide
  have hdescent : baseEnd_483889 < baseStart_483889 := by decide
  rcases family_descends (prefixWord ++ tailWord_483889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483903 : List Nat := [1, 1, 2, 2, 3, 2, 3, 4, 1, 2, 2]
def baseStart_483903 : Nat := 118140960795 + 483903 * 2 ^ 59
def prefixEnd_483903 : Nat := 4983230072969 + 3 ^ 40 * 483903 * 2
def baseEnd_483903 : Nat := 248474829152725460987077

theorem tailTrace_483903 : CollatzResearch.WordTrace tailWord_483903 prefixEnd_483903 248474829152725460987077 := by
  unfold tailWord_483903
  simp only [CollatzResearch.WordTrace]
  refine ⟨17649392365909549897880363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11766261577273033265253575 17649392365909549897880363)
  ·
    refine ⟨26474088548864324846820545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17649392365909549897880363 26474088548864324846820545)
    ·
      refine ⟨19855566411648243635115409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26474088548864324846820545 19855566411648243635115409)
      ·
        refine ⟨14891674808736182726336557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19855566411648243635115409 14891674808736182726336557)
        ·
          refine ⟨5584378053276068522376209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14891674808736182726336557 5584378053276068522376209)
          ·
            refine ⟨4188283539957051391782157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5584378053276068522376209 4188283539957051391782157)
            ·
              refine ⟨1570606327483894271918309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4188283539957051391782157 1570606327483894271918309)
              ·
                refine ⟨294488686403230175984683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1570606327483894271918309 294488686403230175984683)
                ·
                  refine ⟨441733029604845263977025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294488686403230175984683 441733029604845263977025)
                  ·
                    refine ⟨331299772203633947982769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 441733029604845263977025 331299772203633947982769)
                    ·
                      refine ⟨248474829152725460987077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 331299772203633947982769 248474829152725460987077)
                      ·
                        rfl

theorem cell23_483903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 1, 2, 2].length) (baseStart_483903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483903 prefixEnd_483903 := by exact prefixLift 483903
  have htrace : WordTrace (prefixWord ++ tailWord_483903) baseStart_483903 baseEnd_483903 := by
    simpa [prefixWord, tailWord_483903, baseEnd_483903] using wordTrace_append hprefix tailTrace_483903
  have hstable : (prefixWord ++ tailWord_483903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483903).length < 2 ^ (prefixWord ++ tailWord_483903).sum := by decide
  have hdescent : baseEnd_483903 < baseStart_483903 := by decide
  rcases family_descends (prefixWord ++ tailWord_483903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483922 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_483922 : Nat := 118140960795 + 483922 * 2 ^ 59
def prefixEnd_483922 : Nat := 4983230072969 + 3 ^ 40 * 483922 * 2
def baseEnd_483922 : Nat := 82828195095053628883163

theorem tailTrace_483922 : CollatzResearch.WordTrace tailWord_483922 prefixEnd_483922 82828195095053628883163 := by
  unfold tailWord_483922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4412521338210179035705505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11766723568560477428548013 4412521338210179035705505)
  ·
    refine ⟨3309391003657634276779129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4412521338210179035705505 3309391003657634276779129)
    ·
      refine ⟨2482043252743225707584347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3309391003657634276779129 2482043252743225707584347)
      ·
        refine ⟨3723064879114838561376521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2482043252743225707584347 3723064879114838561376521)
        ·
          refine ⟨2792298659336128921032391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3723064879114838561376521 2792298659336128921032391)
          ·
            refine ⟨4188447989004193381548587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792298659336128921032391 4188447989004193381548587)
            ·
              refine ⟨6282671983506290072322881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4188447989004193381548587 6282671983506290072322881)
              ·
                refine ⟨4712003987629717554242161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6282671983506290072322881 4712003987629717554242161)
                ·
                  refine ⟨3534002990722288165681621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4712003987629717554242161 3534002990722288165681621)
                  ·
                    refine ⟨82828195095053628883163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3534002990722288165681621 82828195095053628883163)
                    ·
                      rfl

theorem cell23_483922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_483922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483922 prefixEnd_483922 := by exact prefixLift 483922
  have htrace : WordTrace (prefixWord ++ tailWord_483922) baseStart_483922 baseEnd_483922 := by
    simpa [prefixWord, tailWord_483922, baseEnd_483922] using wordTrace_append hprefix tailTrace_483922
  have hstable : (prefixWord ++ tailWord_483922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483922).length < 2 ^ (prefixWord ++ tailWord_483922).sum := by decide
  have hdescent : baseEnd_483922 < baseStart_483922 := by decide
  rcases family_descends (prefixWord ++ tailWord_483922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483934 : List Nat := [4, 4, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_483934 : Nat := 118140960795 + 483934 * 2 ^ 59
def prefixEnd_483934 : Nat := 4983230072969 + 3 ^ 40 * 483934 * 2
def baseEnd_483934 : Nat := 82830249017671613233145

theorem tailTrace_483934 : CollatzResearch.WordTrace tailWord_483934 prefixEnd_483934 82830249017671613233145 := by
  unfold tailWord_483934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2206315378599655274032357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11767015352531494794839237 2206315378599655274032357)
  ·
    refine ⟨413684133487435363881067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2206315378599655274032357 413684133487435363881067)
    ·
      refine ⟨620526200231153045821601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413684133487435363881067 620526200231153045821601)
      ·
        refine ⟨465394650173364784366201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620526200231153045821601 465394650173364784366201)
        ·
          refine ⟨349045987630023588274651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465394650173364784366201 349045987630023588274651)
          ·
            refine ⟨523568981445035382411977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349045987630023588274651 523568981445035382411977)
            ·
              refine ⟨392676736083776536808983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523568981445035382411977 392676736083776536808983)
              ·
                refine ⟨589015104125664805213475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392676736083776536808983 589015104125664805213475)
                ·
                  refine ⟨883522656188497207820213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589015104125664805213475 883522656188497207820213)
                  ·
                    refine ⟨82830249017671613233145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 883522656188497207820213 82830249017671613233145)
                    ·
                      rfl

theorem cell23_483934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_483934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483934 prefixEnd_483934 := by exact prefixLift 483934
  have htrace : WordTrace (prefixWord ++ tailWord_483934) baseStart_483934 baseEnd_483934 := by
    simpa [prefixWord, tailWord_483934, baseEnd_483934] using wordTrace_append hprefix tailTrace_483934
  have hstable : (prefixWord ++ tailWord_483934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483934).length < 2 ^ (prefixWord ++ tailWord_483934).sum := by decide
  have hdescent : baseEnd_483934 < baseStart_483934 := by decide
  rcases family_descends (prefixWord ++ tailWord_483934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483959 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 3, 4, 2]
def baseStart_483959 : Nat := 118140960795 + 483959 * 2 ^ 59
def prefixEnd_483959 : Nat := 4983230072969 + 3 ^ 40 * 483959 * 2
def baseEnd_483959 : Nat := 248503584069377241886819

theorem tailTrace_483959 : CollatzResearch.WordTrace tailWord_483959 prefixEnd_483959 248503584069377241886819 := by
  unfold tailWord_483959
  simp only [CollatzResearch.WordTrace]
  refine ⟨17651434853706671461918931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11767623235804447641279287 17651434853706671461918931)
  ·
    refine ⟨26477152280560007192878397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17651434853706671461918931 26477152280560007192878397)
    ·
      refine ⟨9928932105210002697329399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26477152280560007192878397 9928932105210002697329399)
      ·
        refine ⟨14893398157815004045994099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9928932105210002697329399 14893398157815004045994099)
        ·
          refine ⟨22340097236722506068991149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14893398157815004045994099 22340097236722506068991149)
          ·
            refine ⟨8377536463770939775871681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22340097236722506068991149 8377536463770939775871681)
            ·
              refine ⟨6283152347828204831903761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8377536463770939775871681 6283152347828204831903761)
              ·
                refine ⟨4712364260871153623927821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6283152347828204831903761 4712364260871153623927821)
                ·
                  refine ⟨1767136597826682608972933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4712364260871153623927821 1767136597826682608972933)
                  ·
                    refine ⟨331338112092502989182425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1767136597826682608972933 331338112092502989182425)
                    ·
                      refine ⟨248503584069377241886819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 331338112092502989182425 248503584069377241886819)
                      ·
                        rfl

theorem cell23_483959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 4, 2].length) (baseStart_483959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_483959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_483959 prefixEnd_483959 := by exact prefixLift 483959
  have htrace : WordTrace (prefixWord ++ tailWord_483959) baseStart_483959 baseEnd_483959 := by
    simpa [prefixWord, tailWord_483959, baseEnd_483959] using wordTrace_append hprefix tailTrace_483959
  have hstable : (prefixWord ++ tailWord_483959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483959).length < 2 ^ (prefixWord ++ tailWord_483959).sum := by decide
  have hdescent : baseEnd_483959 < baseStart_483959 := by decide
  rcases family_descends (prefixWord ++ tailWord_483959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484046 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_484046 : Nat := 118140960795 + 484046 * 2 ^ 59
def prefixEnd_484046 : Nat := 4983230072969 + 3 ^ 40 * 484046 * 2
def baseEnd_484046 : Nat := 82849418962106133832973

theorem tailTrace_484046 : CollatzResearch.WordTrace tailWord_484046 prefixEnd_484046 82849418962106133832973 := by
  unfold tailWord_484046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2206826000548935665041999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11769738669594323546890661 2206826000548935665041999)
  ·
    refine ⟨3310239000823403497562999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2206826000548935665041999 3310239000823403497562999)
    ·
      refine ⟨4965358501235105246344499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3310239000823403497562999 4965358501235105246344499)
      ·
        refine ⟨7448037751852657869516749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4965358501235105246344499 7448037751852657869516749)
        ·
          refine ⟨2793014156944746701068781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7448037751852657869516749 2793014156944746701068781)
          ·
            refine ⟨1047380308854280012900793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2793014156944746701068781 1047380308854280012900793)
            ·
              refine ⟨785535231640710009675595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1047380308854280012900793 785535231640710009675595)
              ·
                refine ⟨1178302847461065014513393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785535231640710009675595 1178302847461065014513393)
                ·
                  refine ⟨883727135595798760885045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1178302847461065014513393 883727135595798760885045)
                  ·
                    refine ⟨82849418962106133832973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 883727135595798760885045 82849418962106133832973)
                    ·
                      rfl

theorem cell23_484046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_484046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484046 prefixEnd_484046 := by exact prefixLift 484046
  have htrace : WordTrace (prefixWord ++ tailWord_484046) baseStart_484046 baseEnd_484046 := by
    simpa [prefixWord, tailWord_484046, baseEnd_484046] using wordTrace_append hprefix tailTrace_484046
  have hstable : (prefixWord ++ tailWord_484046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484046).length < 2 ^ (prefixWord ++ tailWord_484046).sum := by decide
  have hdescent : baseEnd_484046 < baseStart_484046 := by decide
  rcases family_descends (prefixWord ++ tailWord_484046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484086 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_484086 : Nat := 118140960795 + 484086 * 2 ^ 59
def prefixEnd_484086 : Nat := 4983230072969 + 3 ^ 40 * 484086 * 2
def baseEnd_484086 : Nat := 248568796112498244998735

theorem tailTrace_484086 : CollatzResearch.WordTrace tailWord_484086 prefixEnd_484086 248568796112498244998735 := by
  unfold tailWord_484086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103504182765410759487007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11770711282831048101194741 1103504182765410759487007)
  ·
    refine ⟨1655256274148116139230511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1103504182765410759487007 1655256274148116139230511)
    ·
      refine ⟨2482884411222174208845767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655256274148116139230511 2482884411222174208845767)
      ·
        refine ⟨3724326616833261313268651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2482884411222174208845767 3724326616833261313268651)
        ·
          refine ⟨5586489925249891969902977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724326616833261313268651 5586489925249891969902977)
          ·
            refine ⟨4189867443937418977427233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5586489925249891969902977 4189867443937418977427233)
            ·
              refine ⟨3142400582953064233070425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4189867443937418977427233 3142400582953064233070425)
              ·
                refine ⟨2356800437214798174802819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3142400582953064233070425 2356800437214798174802819)
                ·
                  refine ⟨3535200655822197262204229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356800437214798174802819 3535200655822197262204229)
                  ·
                    refine ⟨662850122966661986663293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3535200655822197262204229 662850122966661986663293)
                    ·
                      refine ⟨248568796112498244998735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 662850122966661986663293 248568796112498244998735)
                      ·
                        rfl

theorem cell23_484086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_484086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484086 prefixEnd_484086 := by exact prefixLift 484086
  have htrace : WordTrace (prefixWord ++ tailWord_484086) baseStart_484086 baseEnd_484086 := by
    simpa [prefixWord, tailWord_484086, baseEnd_484086] using wordTrace_append hprefix tailTrace_484086
  have hstable : (prefixWord ++ tailWord_484086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484086).length < 2 ^ (prefixWord ++ tailWord_484086).sum := by decide
  have hdescent : baseEnd_484086 < baseStart_484086 := by decide
  rcases family_descends (prefixWord ++ tailWord_484086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484103 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_484103 : Nat := 118140960795 + 484103 * 2 ^ 59
def prefixEnd_484103 : Nat := 4983230072969 + 3 ^ 40 * 484103 * 2
def baseEnd_484103 : Nat := 248577525283624678486157

theorem tailTrace_484103 : CollatzResearch.WordTrace tailWord_484103 prefixEnd_484103 248577525283624678486157 := by
  unfold tailWord_484103
  simp only [CollatzResearch.WordTrace]
  refine ⟨17656686965184984055160963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11771124643456656036773975 17656686965184984055160963)
  ·
    refine ⟨26485030447777476082741445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17656686965184984055160963 26485030447777476082741445)
    ·
      refine ⟨4965943208958276765514021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26485030447777476082741445 4965943208958276765514021)
      ·
        refine ⟨931114351679676893533879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4965943208958276765514021 931114351679676893533879)
        ·
          refine ⟨1396671527519515340300819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931114351679676893533879 1396671527519515340300819)
          ·
            refine ⟨2095007291279273010451229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396671527519515340300819 2095007291279273010451229)
            ·
              refine ⟨785627734229727378919211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2095007291279273010451229 785627734229727378919211)
              ·
                refine ⟨1178441601344591068378817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785627734229727378919211 1178441601344591068378817)
                ·
                  refine ⟨883831201008443301284113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1178441601344591068378817 883831201008443301284113)
                  ·
                    refine ⟨662873400756332475963085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 883831201008443301284113 662873400756332475963085)
                    ·
                      refine ⟨248577525283624678486157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 662873400756332475963085 248577525283624678486157)
                      ·
                        rfl

theorem cell23_484103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_484103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484103 prefixEnd_484103 := by exact prefixLift 484103
  have htrace : WordTrace (prefixWord ++ tailWord_484103) baseStart_484103 baseEnd_484103 := by
    simpa [prefixWord, tailWord_484103, baseEnd_484103] using wordTrace_append hprefix tailTrace_484103
  have hstable : (prefixWord ++ tailWord_484103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484103).length < 2 ^ (prefixWord ++ tailWord_484103).sum := by decide
  have hdescent : baseEnd_484103 < baseStart_484103 := by decide
  rcases family_descends (prefixWord ++ tailWord_484103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484133 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 3, 1, 3]
def baseStart_484133 : Nat := 118140960795 + 484133 * 2 ^ 59
def prefixEnd_484133 : Nat := 4983230072969 + 3 ^ 40 * 484133 * 2
def baseEnd_484133 : Nat := 248592929703259561111019

theorem tailTrace_484133 : CollatzResearch.WordTrace tailWord_484133 prefixEnd_484133 248592929703259561111019 := by
  unfold tailWord_484133
  simp only [CollatzResearch.WordTrace]
  refine ⟨17657781155076299178753053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11771854103384199452502035 17657781155076299178753053)
  ·
    refine ⟨6621667933153612192032395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17657781155076299178753053 6621667933153612192032395)
    ·
      refine ⟨9932501899730418288048593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6621667933153612192032395 9932501899730418288048593)
      ·
        refine ⟨7449376424797813716036445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9932501899730418288048593 7449376424797813716036445)
        ·
          refine ⟨2793516159299180143513667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7449376424797813716036445 2793516159299180143513667)
          ·
            refine ⟨4190274238948770215270501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793516159299180143513667 4190274238948770215270501)
            ·
              refine ⟨785676419802894415363219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4190274238948770215270501 785676419802894415363219)
              ·
                refine ⟨1178514629704341623044829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785676419802894415363219 1178514629704341623044829)
                ·
                  refine ⟨441942986139128108641811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1178514629704341623044829 441942986139128108641811)
                  ·
                    refine ⟨662914479208692162962717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 441942986139128108641811 662914479208692162962717)
                    ·
                      refine ⟨248592929703259561111019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 662914479208692162962717 248592929703259561111019)
                      ·
                        rfl

theorem cell23_484133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_484133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484133 prefixEnd_484133 := by exact prefixLift 484133
  have htrace : WordTrace (prefixWord ++ tailWord_484133) baseStart_484133 baseEnd_484133 := by
    simpa [prefixWord, tailWord_484133, baseEnd_484133] using wordTrace_append hprefix tailTrace_484133
  have hstable : (prefixWord ++ tailWord_484133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484133).length < 2 ^ (prefixWord ++ tailWord_484133).sum := by decide
  have hdescent : baseEnd_484133 < baseStart_484133 := by decide
  rcases family_descends (prefixWord ++ tailWord_484133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484156 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 1, 8, 2]
def baseStart_484156 : Nat := 118140960795 + 484156 * 2 ^ 59
def prefixEnd_484156 : Nat := 4983230072969 + 3 ^ 40 * 484156 * 2
def baseEnd_484156 : Nat := 248604739758312971123413

theorem tailTrace_484156 : CollatzResearch.WordTrace tailWord_484156 prefixEnd_484156 248604739758312971123413 := by
  unfold tailWord_484156
  simp only [CollatzResearch.WordTrace]
  refine ⟨8829310016996487053420161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11772413355995316071226881 8829310016996487053420161)
  ·
    refine ⟨6621982512747365290065121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8829310016996487053420161 6621982512747365290065121)
    ·
      refine ⟨4966486884560523967548841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6621982512747365290065121 4966486884560523967548841)
      ·
        refine ⟨3724865163420392975661631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4966486884560523967548841 3724865163420392975661631)
        ·
          refine ⟨5587297745130589463492447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724865163420392975661631 5587297745130589463492447)
          ·
            refine ⟨8380946617695884195238671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5587297745130589463492447 8380946617695884195238671)
            ·
              refine ⟨12571419926543826292858007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8380946617695884195238671 12571419926543826292858007)
              ·
                refine ⟨18857129889815739439287011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12571419926543826292858007 18857129889815739439287011)
                ·
                  refine ⟨28285694834723609158930517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18857129889815739439287011 28285694834723609158930517)
                  ·
                    refine ⟨331472986344417294831217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28285694834723609158930517 331472986344417294831217)
                    ·
                      refine ⟨248604739758312971123413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 331472986344417294831217 248604739758312971123413)
                      ·
                        rfl

theorem cell23_484156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_484156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484156 prefixEnd_484156 := by exact prefixLift 484156
  have htrace : WordTrace (prefixWord ++ tailWord_484156) baseStart_484156 baseEnd_484156 := by
    simpa [prefixWord, tailWord_484156, baseEnd_484156] using wordTrace_append hprefix tailTrace_484156
  have hstable : (prefixWord ++ tailWord_484156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484156).length < 2 ^ (prefixWord ++ tailWord_484156).sum := by decide
  have hdescent : baseEnd_484156 < baseStart_484156 := by decide
  rcases family_descends (prefixWord ++ tailWord_484156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484196 : List Nat := [2, 3, 1, 1, 4, 2, 2, 8]
def baseStart_484196 : Nat := 118140960795 + 484196 * 2 ^ 59
def prefixEnd_484196 : Nat := 4983230072969 + 3 ^ 40 * 484196 * 2
def baseEnd_484196 : Nat := 9208343666092326467527

theorem tailTrace_484196 : CollatzResearch.WordTrace tailWord_484196 prefixEnd_484196 9208343666092326467527 := by
  unfold tailWord_484196
  simp only [CollatzResearch.WordTrace]
  refine ⟨8830039476924030469148221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11773385969232040625530961 8830039476924030469148221)
  ·
    refine ⟨3311264803846511425930583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8830039476924030469148221 3311264803846511425930583)
    ·
      refine ⟨4966897205769767138895875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3311264803846511425930583 4966897205769767138895875)
      ·
        refine ⟨7450345808654650708343813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4966897205769767138895875 7450345808654650708343813)
        ·
          refine ⟨1396939839122747007814465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7450345808654650708343813 1396939839122747007814465)
          ·
            refine ⟨1047704879342060255860849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1396939839122747007814465 1047704879342060255860849)
            ·
              refine ⟨785778659506545191895637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1047704879342060255860849 785778659506545191895637)
              ·
                refine ⟨9208343666092326467527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 785778659506545191895637 9208343666092326467527)
                ·
                  rfl

theorem cell23_484196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 8].length) (baseStart_484196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484196 prefixEnd_484196 := by exact prefixLift 484196
  have htrace : WordTrace (prefixWord ++ tailWord_484196) baseStart_484196 baseEnd_484196 := by
    simpa [prefixWord, tailWord_484196, baseEnd_484196] using wordTrace_append hprefix tailTrace_484196
  have hstable : (prefixWord ++ tailWord_484196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484196).length < 2 ^ (prefixWord ++ tailWord_484196).sum := by decide
  have hdescent : baseEnd_484196 < baseStart_484196 := by decide
  rcases family_descends (prefixWord ++ tailWord_484196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484200 : List Nat := [2, 1, 4, 2, 1, 2, 4, 1, 2, 4]
def baseStart_484200 : Nat := 118140960795 + 484200 * 2 ^ 59
def prefixEnd_484200 : Nat := 4983230072969 + 3 ^ 40 * 484200 * 2
def baseEnd_484200 : Nat := 82875777635703599657737

theorem tailTrace_484200 : CollatzResearch.WordTrace tailWord_484200 prefixEnd_484200 82875777635703599657737 := by
  unfold tailWord_484200
  simp only [CollatzResearch.WordTrace]
  refine ⟨8830112422916784810721027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11773483230555713080961369 8830112422916784810721027)
  ·
    refine ⟨13245168634375177216081541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8830112422916784810721027 13245168634375177216081541)
    ·
      refine ⟨2483469118945345728015289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13245168634375177216081541 2483469118945345728015289)
      ·
        refine ⟨1862601839209009296011467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2483469118945345728015289 1862601839209009296011467)
        ·
          refine ⟨2793902758813513944017201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1862601839209009296011467 2793902758813513944017201)
          ·
            refine ⟨2095427069110135458012901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2793902758813513944017201 2095427069110135458012901)
            ·
              refine ⟨392892575458150398377419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2095427069110135458012901 392892575458150398377419)
              ·
                refine ⟨589338863187225597566129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392892575458150398377419 589338863187225597566129)
                ·
                  refine ⟨442004147390419198174597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589338863187225597566129 442004147390419198174597)
                  ·
                    refine ⟨82875777635703599657737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 442004147390419198174597 82875777635703599657737)
                    ·
                      rfl

theorem cell23_484200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_484200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484200 prefixEnd_484200 := by exact prefixLift 484200
  have htrace : WordTrace (prefixWord ++ tailWord_484200) baseStart_484200 baseEnd_484200 := by
    simpa [prefixWord, tailWord_484200, baseEnd_484200] using wordTrace_append hprefix tailTrace_484200
  have hstable : (prefixWord ++ tailWord_484200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484200).length < 2 ^ (prefixWord ++ tailWord_484200).sum := by decide
  have hdescent : baseEnd_484200 < baseStart_484200 := by decide
  rcases family_descends (prefixWord ++ tailWord_484200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484219 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 5]
def baseStart_484219 : Nat := 118140960795 + 484219 * 2 ^ 59
def prefixEnd_484219 : Nat := 4983230072969 + 3 ^ 40 * 484219 * 2
def baseEnd_484219 : Nat := 248637089039546224635623

theorem tailTrace_484219 : CollatzResearch.WordTrace tailWord_484219 prefixEnd_484219 248637089039546224635623 := by
  unfold tailWord_484219
  simp only [CollatzResearch.WordTrace]
  refine ⟨17660917832764735866383711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11773945221843157244255807 17660917832764735866383711)
  ·
    refine ⟨26491376749147103799575567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17660917832764735866383711 26491376749147103799575567)
    ·
      refine ⟨39737065123720655699363351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26491376749147103799575567 39737065123720655699363351)
      ·
        refine ⟨59605597685580983549045027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39737065123720655699363351 59605597685580983549045027)
        ·
          refine ⟨89408396528371475323567541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59605597685580983549045027 89408396528371475323567541)
          ·
            refine ⟨8382037174534825811584457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89408396528371475323567541 8382037174534825811584457)
            ·
              refine ⟨6286527880901119358688343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8382037174534825811584457 6286527880901119358688343)
              ·
                refine ⟨9429791821351679038032515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6286527880901119358688343 9429791821351679038032515)
                ·
                  refine ⟨14144687732027518557048773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9429791821351679038032515 14144687732027518557048773)
                  ·
                    refine ⟨2652128949755159729446645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14144687732027518557048773 2652128949755159729446645)
                    ·
                      refine ⟨248637089039546224635623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2652128949755159729446645 248637089039546224635623)
                      ·
                        rfl

theorem cell23_484219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 5].length) (baseStart_484219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484219 prefixEnd_484219 := by exact prefixLift 484219
  have htrace : WordTrace (prefixWord ++ tailWord_484219) baseStart_484219 baseEnd_484219 := by
    simpa [prefixWord, tailWord_484219, baseEnd_484219] using wordTrace_append hprefix tailTrace_484219
  have hstable : (prefixWord ++ tailWord_484219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484219).length < 2 ^ (prefixWord ++ tailWord_484219).sum := by decide
  have hdescent : baseEnd_484219 < baseStart_484219 := by decide
  rcases family_descends (prefixWord ++ tailWord_484219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484278 : List Nat := [5, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_484278 : Nat := 118140960795 + 484278 * 2 ^ 59
def prefixEnd_484278 : Nat := 4983230072969 + 3 ^ 40 * 484278 * 2
def baseEnd_484278 : Nat := 248667384398161493797853

theorem tailTrace_484278 : CollatzResearch.WordTrace tailWord_484278 prefixEnd_484278 248667384398161493797853 := by
  unfold tailWord_484278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103941858721936808923843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11775379826367325961854325 1103941858721936808923843)
  ·
    refine ⟨1655912788082905213385765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1103941858721936808923843 1655912788082905213385765)
    ·
      refine ⟨310483647765544727509831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1655912788082905213385765 310483647765544727509831)
      ·
        refine ⟨465725471648317091264747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310483647765544727509831 465725471648317091264747)
        ·
          refine ⟨698588207472475636897121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465725471648317091264747 698588207472475636897121)
          ·
            refine ⟨523941155604356727672841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 698588207472475636897121 523941155604356727672841)
            ·
              refine ⟨392955866703267545754631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523941155604356727672841 392955866703267545754631)
              ·
                refine ⟨589433800054901318631947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392955866703267545754631 589433800054901318631947)
                ·
                  refine ⟨884150700082351977947921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589433800054901318631947 884150700082351977947921)
                  ·
                    refine ⟨663113025061763983460941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 884150700082351977947921 663113025061763983460941)
                    ·
                      refine ⟨248667384398161493797853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 663113025061763983460941 248667384398161493797853)
                      ·
                        rfl

theorem cell23_484278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_484278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484278 prefixEnd_484278 := by exact prefixLift 484278
  have htrace : WordTrace (prefixWord ++ tailWord_484278) baseStart_484278 baseEnd_484278 := by
    simpa [prefixWord, tailWord_484278, baseEnd_484278] using wordTrace_append hprefix tailTrace_484278
  have hstable : (prefixWord ++ tailWord_484278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484278).length < 2 ^ (prefixWord ++ tailWord_484278).sum := by decide
  have hdescent : baseEnd_484278 < baseStart_484278 := by decide
  rcases family_descends (prefixWord ++ tailWord_484278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484286 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 9]
def baseStart_484286 : Nat := 118140960795 + 484286 * 2 ^ 59
def prefixEnd_484286 : Nat := 4983230072969 + 3 ^ 40 * 484286 * 2
def baseEnd_484286 : Nat := 27630165804821940277535

theorem tailTrace_484286 : CollatzResearch.WordTrace tailWord_484286 prefixEnd_484286 27630165804821940277535 := by
  unfold tailWord_484286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2207920190440250788634089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11775574349014670872715141 2207920190440250788634089)
  ·
    refine ⟨1655940142830188091475567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2207920190440250788634089 1655940142830188091475567)
    ·
      refine ⟨2483910214245282137213351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655940142830188091475567 2483910214245282137213351)
      ·
        refine ⟨3725865321367923205820027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2483910214245282137213351 3725865321367923205820027)
        ·
          refine ⟨5588797982051884808730041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3725865321367923205820027 5588797982051884808730041)
          ·
            refine ⟨4191598486538913606547531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5588797982051884808730041 4191598486538913606547531)
            ·
              refine ⟨6287397729808370409821297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191598486538913606547531 6287397729808370409821297)
              ·
                refine ⟨4715548297356277807365973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6287397729808370409821297 4715548297356277807365973)
                ·
                  refine ⟨27630165804821940277535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4715548297356277807365973 27630165804821940277535)
                  ·
                    rfl

theorem cell23_484286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_484286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484286 prefixEnd_484286 := by exact prefixLift 484286
  have htrace : WordTrace (prefixWord ++ tailWord_484286) baseStart_484286 baseEnd_484286 := by
    simpa [prefixWord, tailWord_484286, baseEnd_484286] using wordTrace_append hprefix tailTrace_484286
  have hstable : (prefixWord ++ tailWord_484286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484286).length < 2 ^ (prefixWord ++ tailWord_484286).sum := by decide
  have hdescent : baseEnd_484286 < baseStart_484286 := by decide
  rcases family_descends (prefixWord ++ tailWord_484286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484303 : List Nat := [1, 1, 2, 1, 1, 6, 2, 4, 5]
def baseStart_484303 : Nat := 118140960795 + 484303 * 2 ^ 59
def prefixEnd_484303 : Nat := 4983230072969 + 3 ^ 40 * 484303 * 2
def baseEnd_484303 : Nat := 27631135712724877331693

theorem tailTrace_484303 : CollatzResearch.WordTrace tailWord_484303 prefixEnd_484303 27631135712724877331693 := by
  unfold tailWord_484303
  simp only [CollatzResearch.WordTrace]
  refine ⟨17663981564460418212441563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11775987709640278808294375 17663981564460418212441563)
  ·
    refine ⟨26495972346690627318662345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17663981564460418212441563 26495972346690627318662345)
    ·
      refine ⟨19871979260017970488996759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26495972346690627318662345 19871979260017970488996759)
      ·
        refine ⟨29807968890026955733495139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19871979260017970488996759 29807968890026955733495139)
        ·
          refine ⟨44711953335040433600242709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29807968890026955733495139 44711953335040433600242709)
          ·
            refine ⟨2095872812580020325011377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44711953335040433600242709 2095872812580020325011377)
            ·
              refine ⟨1571904609435015243758533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2095872812580020325011377 1571904609435015243758533)
              ·
                refine ⟨294732114269065358204725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1571904609435015243758533 294732114269065358204725)
                ·
                  refine ⟨27631135712724877331693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 294732114269065358204725 27631135712724877331693)
                  ·
                    rfl

theorem cell23_484303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 5].length) (baseStart_484303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484303 prefixEnd_484303 := by exact prefixLift 484303
  have htrace : WordTrace (prefixWord ++ tailWord_484303) baseStart_484303 baseEnd_484303 := by
    simpa [prefixWord, tailWord_484303, baseEnd_484303] using wordTrace_append hprefix tailTrace_484303
  have hstable : (prefixWord ++ tailWord_484303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484303).length < 2 ^ (prefixWord ++ tailWord_484303).sum := by decide
  have hdescent : baseEnd_484303 < baseStart_484303 := by decide
  rcases family_descends (prefixWord ++ tailWord_484303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484310 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_484310 : Nat := 118140960795 + 484310 * 2 ^ 59
def prefixEnd_484310 : Nat := 4983230072969 + 3 ^ 40 * 484310 * 2
def baseEnd_484310 : Nat := 248683815779105368597705

theorem tailTrace_484310 : CollatzResearch.WordTrace tailWord_484310 prefixEnd_484310 248683815779105368597705 := by
  unfold tailWord_484310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104014804714691150496649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11776157916956705605297589 1104014804714691150496649)
  ·
    refine ⟨828011103536018362872487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1104014804714691150496649 828011103536018362872487)
    ·
      refine ⟨1242016655304027544308731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828011103536018362872487 1242016655304027544308731)
      ·
        refine ⟨1863024982956041316463097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242016655304027544308731 1863024982956041316463097)
        ·
          refine ⟨1397268737217030987347323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1863024982956041316463097 1397268737217030987347323)
          ·
            refine ⟨2095903105825546481020985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397268737217030987347323 2095903105825546481020985)
            ·
              refine ⟨1571927329369159860765739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2095903105825546481020985 1571927329369159860765739)
              ·
                refine ⟨2357890994053739791148609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571927329369159860765739 2357890994053739791148609)
                ·
                  refine ⟨1768418245540304843361457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2357890994053739791148609 1768418245540304843361457)
                  ·
                    refine ⟨1326313684155228632521093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1768418245540304843361457 1326313684155228632521093)
                    ·
                      refine ⟨248683815779105368597705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1326313684155228632521093 248683815779105368597705)
                      ·
                        rfl

theorem cell23_484310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_484310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484310 prefixEnd_484310 := by exact prefixLift 484310
  have htrace : WordTrace (prefixWord ++ tailWord_484310) baseStart_484310 baseEnd_484310 := by
    simpa [prefixWord, tailWord_484310, baseEnd_484310] using wordTrace_append hprefix tailTrace_484310
  have hstable : (prefixWord ++ tailWord_484310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484310).length < 2 ^ (prefixWord ++ tailWord_484310).sum := by decide
  have hdescent : baseEnd_484310 < baseStart_484310 := by decide
  rcases family_descends (prefixWord ++ tailWord_484310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484313 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 2, 3, 3]
def baseStart_484313 : Nat := 118140960795 + 484313 * 2 ^ 59
def prefixEnd_484313 : Nat := 4983230072969 + 3 ^ 40 * 484313 * 2
def baseEnd_484313 : Nat := 248685356221068856860191

theorem tailTrace_484313 : CollatzResearch.WordTrace tailWord_484313 prefixEnd_484313 248685356221068856860191 := by
  unfold tailWord_484313
  simp only [CollatzResearch.WordTrace]
  refine ⟨17664346294424189920305593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11776230862949459946870395 17664346294424189920305593)
  ·
    refine ⟨13248259720818142440229195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17664346294424189920305593 13248259720818142440229195)
    ·
      refine ⟨19872389581227213660343793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13248259720818142440229195 19872389581227213660343793)
      ·
        refine ⟨14904292185920410245257845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19872389581227213660343793 14904292185920410245257845)
        ·
          refine ⟨1397277392430038460492923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14904292185920410245257845 1397277392430038460492923)
          ·
            refine ⟨2095916088645057690739385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397277392430038460492923 2095916088645057690739385)
            ·
              refine ⟨1571937066483793268054539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2095916088645057690739385 1571937066483793268054539)
              ·
                refine ⟨2357905599725689902081809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571937066483793268054539 2357905599725689902081809)
                ·
                  refine ⟨1768429199794267426561357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2357905599725689902081809 1768429199794267426561357)
                  ·
                    refine ⟨663160949922850284960509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1768429199794267426561357 663160949922850284960509)
                    ·
                      refine ⟨248685356221068856860191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 663160949922850284960509 248685356221068856860191)
                      ·
                        rfl

theorem cell23_484313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_484313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484313 prefixEnd_484313 := by exact prefixLift 484313
  have htrace : WordTrace (prefixWord ++ tailWord_484313) baseStart_484313 baseEnd_484313 := by
    simpa [prefixWord, tailWord_484313, baseEnd_484313] using wordTrace_append hprefix tailTrace_484313
  have hstable : (prefixWord ++ tailWord_484313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484313).length < 2 ^ (prefixWord ++ tailWord_484313).sum := by decide
  have hdescent : baseEnd_484313 < baseStart_484313 := by decide
  rcases family_descends (prefixWord ++ tailWord_484313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484314 : List Nat := [3, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2]
def baseStart_484314 : Nat := 118140960795 + 484314 * 2 ^ 59
def prefixEnd_484314 : Nat := 4983230072969 + 3 ^ 40 * 484314 * 2
def baseEnd_484314 : Nat := 248685869701723352947687

theorem tailTrace_484314 : CollatzResearch.WordTrace tailWord_484314 prefixEnd_484314 248685869701723352947687 := by
  unfold tailWord_484314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4416095691855141772772999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11776255178280378060727997 4416095691855141772772999)
  ·
    refine ⟨6624143537782712659159499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4416095691855141772772999 6624143537782712659159499)
    ·
      refine ⟨9936215306674068988739249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6624143537782712659159499 9936215306674068988739249)
      ·
        refine ⟨7452161480005551741554437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9936215306674068988739249 7452161480005551741554437)
        ·
          refine ⟨1397280277501040951541457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7452161480005551741554437 1397280277501040951541457)
          ·
            refine ⟨1047960208125780713656093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1397280277501040951541457 1047960208125780713656093)
            ·
              refine ⟨392985078047167767621035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1047960208125780713656093 392985078047167767621035)
              ·
                refine ⟨589477617070751651431553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392985078047167767621035 589477617070751651431553)
                ·
                  refine ⟨442108212803063738573665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589477617070751651431553 442108212803063738573665)
                  ·
                    refine ⟨331581159602297803930249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 442108212803063738573665 331581159602297803930249)
                    ·
                      refine ⟨248685869701723352947687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 331581159602297803930249 248685869701723352947687)
                      ·
                        rfl

theorem cell23_484314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_484314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484314 prefixEnd_484314 := by exact prefixLift 484314
  have htrace : WordTrace (prefixWord ++ tailWord_484314) baseStart_484314 baseEnd_484314 := by
    simpa [prefixWord, tailWord_484314, baseEnd_484314] using wordTrace_append hprefix tailTrace_484314
  have hstable : (prefixWord ++ tailWord_484314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484314).length < 2 ^ (prefixWord ++ tailWord_484314).sum := by decide
  have hdescent : baseEnd_484314 < baseStart_484314 := by decide
  rcases family_descends (prefixWord ++ tailWord_484314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484353 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_484353 : Nat := 118140960795 + 484353 * 2 ^ 59
def prefixEnd_484353 : Nat := 4983230072969 + 3 ^ 40 * 484353 * 2
def baseEnd_484353 : Nat := 248705895447248700360007

theorem tailTrace_484353 : CollatzResearch.WordTrace tailWord_484353 prefixEnd_484353 248705895447248700360007 := by
  unfold tailWord_484353
  simp only [CollatzResearch.WordTrace]
  refine ⟨17665805214279276751761713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11777203476186184501174475 17665805214279276751761713)
  ·
    refine ⟨13249353910709457563821285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17665805214279276751761713 13249353910709457563821285)
    ·
      refine ⟨2484253858258023293216491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13249353910709457563821285 2484253858258023293216491)
      ·
        refine ⟨3726380787387034939824737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2484253858258023293216491 3726380787387034939824737)
        ·
          refine ⟨2794785590540276204868553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3726380787387034939824737 2794785590540276204868553)
          ·
            refine ⟨2096089192905207153651415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2794785590540276204868553 2096089192905207153651415)
            ·
              refine ⟨3144133789357810730477123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096089192905207153651415 3144133789357810730477123)
              ·
                refine ⟨4716200684036716095715685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144133789357810730477123 4716200684036716095715685)
                ·
                  refine ⟨884287628256884267946691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4716200684036716095715685 884287628256884267946691)
                  ·
                    refine ⟨1326431442385326401920037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 884287628256884267946691 1326431442385326401920037)
                    ·
                      refine ⟨248705895447248700360007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1326431442385326401920037 248705895447248700360007)
                      ·
                        rfl

theorem cell23_484353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_484353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484353 prefixEnd_484353 := by exact prefixLift 484353
  have htrace : WordTrace (prefixWord ++ tailWord_484353) baseStart_484353 baseEnd_484353 := by
    simpa [prefixWord, tailWord_484353, baseEnd_484353] using wordTrace_append hprefix tailTrace_484353
  have hstable : (prefixWord ++ tailWord_484353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484353).length < 2 ^ (prefixWord ++ tailWord_484353).sum := by decide
  have hdescent : baseEnd_484353 < baseStart_484353 := by decide
  rcases family_descends (prefixWord ++ tailWord_484353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484354 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 7]
def baseStart_484354 : Nat := 118140960795 + 484354 * 2 ^ 59
def prefixEnd_484354 : Nat := 4983230072969 + 3 ^ 40 * 484354 * 2
def baseEnd_484354 : Nat := 27634045436433688494167

theorem tailTrace_484354 : CollatzResearch.WordTrace tailWord_484354 prefixEnd_484354 27634045436433688494167 := by
  unfold tailWord_484354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4416460421818913480637029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11777227791517102615032077 4416460421818913480637029)
  ·
    refine ⟨828086329091046277619443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4416460421818913480637029 828086329091046277619443)
    ·
      refine ⟨1242129493636569416429165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828086329091046277619443 1242129493636569416429165)
      ·
        refine ⟨465798560113713531160937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1242129493636569416429165 465798560113713531160937)
        ·
          refine ⟨349348920085285148370703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465798560113713531160937 349348920085285148370703)
          ·
            refine ⟨524023380127927722556055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349348920085285148370703 524023380127927722556055)
            ·
              refine ⟨786035070191891583834083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524023380127927722556055 786035070191891583834083)
              ·
                refine ⟨1179052605287837375751125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786035070191891583834083 1179052605287837375751125)
                ·
                  refine ⟨27634045436433688494167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1179052605287837375751125 27634045436433688494167)
                  ·
                    rfl

theorem cell23_484354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_484354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484354 prefixEnd_484354 := by exact prefixLift 484354
  have htrace : WordTrace (prefixWord ++ tailWord_484354) baseStart_484354 baseEnd_484354 := by
    simpa [prefixWord, tailWord_484354, baseEnd_484354] using wordTrace_append hprefix tailTrace_484354
  have hstable : (prefixWord ++ tailWord_484354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484354).length < 2 ^ (prefixWord ++ tailWord_484354).sum := by decide
  have hdescent : baseEnd_484354 < baseStart_484354 := by decide
  rcases family_descends (prefixWord ++ tailWord_484354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484414 : List Nat := [4, 2, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_484414 : Nat := 118140960795 + 484414 * 2 ^ 59
def prefixEnd_484414 : Nat := 4983230072969 + 3 ^ 40 * 484414 * 2
def baseEnd_484414 : Nat := 82912405922390987232409

theorem tailTrace_484414 : CollatzResearch.WordTrace tailWord_484414 prefixEnd_484414 82912405922390987232409 := by
  unfold tailWord_484414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2208503758382285521216537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11778686711372189446488197 2208503758382285521216537)
  ·
    refine ⟨1656377818786714140912403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2208503758382285521216537 1656377818786714140912403)
    ·
      refine ⟨2484566728180071211368605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1656377818786714140912403 2484566728180071211368605)
      ·
        refine ⟨931712523067526704263227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2484566728180071211368605 931712523067526704263227)
        ·
          refine ⟨1397568784601290056394841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931712523067526704263227 1397568784601290056394841)
          ·
            refine ⟨1048176588450967542296131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1397568784601290056394841 1048176588450967542296131)
            ·
              refine ⟨1572264882676451313444197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048176588450967542296131 1572264882676451313444197)
              ·
                refine ⟨294799665501834621270787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1572264882676451313444197 294799665501834621270787)
                ·
                  refine ⟨442199498252751931906181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294799665501834621270787 442199498252751931906181)
                  ·
                    refine ⟨82912405922390987232409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 442199498252751931906181 82912405922390987232409)
                    ·
                      rfl

theorem cell23_484414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_484414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484414 prefixEnd_484414 := by exact prefixLift 484414
  have htrace : WordTrace (prefixWord ++ tailWord_484414) baseStart_484414 baseEnd_484414 := by
    simpa [prefixWord, tailWord_484414, baseEnd_484414] using wordTrace_append hprefix tailTrace_484414
  have hstable : (prefixWord ++ tailWord_484414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484414).length < 2 ^ (prefixWord ++ tailWord_484414).sum := by decide
  have hdescent : baseEnd_484414 < baseStart_484414 := by decide
  rcases family_descends (prefixWord ++ tailWord_484414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484423 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 3, 5]
def baseStart_484423 : Nat := 118140960795 + 484423 * 2 ^ 59
def prefixEnd_484423 : Nat := 4983230072969 + 3 ^ 40 * 484423 * 2
def baseEnd_484423 : Nat := 82913946364354475494895

theorem tailTrace_484423 : CollatzResearch.WordTrace tailWord_484423 prefixEnd_484423 82913946364354475494895 := by
  unfold tailWord_484423
  simp only [CollatzResearch.WordTrace]
  refine ⟨17668358324025678706809923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11778905549350452471206615 17668358324025678706809923)
  ·
    refine ⟨26502537486038518060214885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17668358324025678706809923 26502537486038518060214885)
    ·
      refine ⟨4969225778632222136290291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26502537486038518060214885 4969225778632222136290291)
      ·
        refine ⟨7453838667948333204435437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969225778632222136290291 7453838667948333204435437)
        ·
          refine ⟨2795189500480624951663289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7453838667948333204435437 2795189500480624951663289)
          ·
            refine ⟨2096392125360468713747467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2795189500480624951663289 2096392125360468713747467)
            ·
              refine ⟨3144588188040703070621201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096392125360468713747467 3144588188040703070621201)
              ·
                refine ⟨2358441141030527302965901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3144588188040703070621201 2358441141030527302965901)
                ·
                  refine ⟨884415427886447738612213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2358441141030527302965901 884415427886447738612213)
                  ·
                    refine ⟨82913946364354475494895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 884415427886447738612213 82913946364354475494895)
                    ·
                      rfl

theorem cell23_484423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_484423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484423 prefixEnd_484423 := by exact prefixLift 484423
  have htrace : WordTrace (prefixWord ++ tailWord_484423) baseStart_484423 baseEnd_484423 := by
    simpa [prefixWord, tailWord_484423, baseEnd_484423] using wordTrace_append hprefix tailTrace_484423
  have hstable : (prefixWord ++ tailWord_484423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484423).length < 2 ^ (prefixWord ++ tailWord_484423).sum := by decide
  have hdescent : baseEnd_484423 < baseStart_484423 := by decide
  rcases family_descends (prefixWord ++ tailWord_484423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484430 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2]
def baseStart_484430 : Nat := 118140960795 + 484430 * 2 ^ 59
def prefixEnd_484430 : Nat := 4983230072969 + 3 ^ 40 * 484430 * 2
def baseEnd_484430 : Nat := 248745433457644899097153

theorem tailTrace_484430 : CollatzResearch.WordTrace tailWord_484430 prefixEnd_484430 248745433457644899097153 := by
  unfold tailWord_484430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2208576704375039862789343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11779075756666879268209829 2208576704375039862789343)
  ·
    refine ⟨3312865056562559794184015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2208576704375039862789343 3312865056562559794184015)
    ·
      refine ⟨4969297584843839691276023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3312865056562559794184015 4969297584843839691276023)
      ·
        refine ⟨7453946377265759536914035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969297584843839691276023 7453946377265759536914035)
        ·
          refine ⟨11180919565898639305371053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7453946377265759536914035 11180919565898639305371053)
          ·
            refine ⟨4192844837211989739514145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11180919565898639305371053 4192844837211989739514145)
            ·
              refine ⟨3144633627908992304635609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4192844837211989739514145 3144633627908992304635609)
              ·
                refine ⟨2358475220931744228476707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3144633627908992304635609 2358475220931744228476707)
                ·
                  refine ⟨3537712831397616342715061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2358475220931744228476707 3537712831397616342715061)
                  ·
                    refine ⟨331660577943526532129537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3537712831397616342715061 331660577943526532129537)
                    ·
                      refine ⟨248745433457644899097153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 331660577943526532129537 248745433457644899097153)
                      ·
                        rfl

theorem cell23_484430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_484430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484430 prefixEnd_484430 := by exact prefixLift 484430
  have htrace : WordTrace (prefixWord ++ tailWord_484430) baseStart_484430 baseEnd_484430 := by
    simpa [prefixWord, tailWord_484430, baseEnd_484430] using wordTrace_append hprefix tailTrace_484430
  have hstable : (prefixWord ++ tailWord_484430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484430).length < 2 ^ (prefixWord ++ tailWord_484430).sum := by decide
  have hdescent : baseEnd_484430 < baseStart_484430 := by decide
  rcases family_descends (prefixWord ++ tailWord_484430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484453 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 1, 6]
def baseStart_484453 : Nat := 118140960795 + 484453 * 2 ^ 59
def prefixEnd_484453 : Nat := 4983230072969 + 3 ^ 40 * 484453 * 2
def baseEnd_484453 : Nat := 82919081170899436369849

theorem tailTrace_484453 : CollatzResearch.WordTrace tailWord_484453 prefixEnd_484453 82919081170899436369849 := by
  unfold tailWord_484453
  simp only [CollatzResearch.WordTrace]
  refine ⟨17669452513916993830402013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11779635009277995886934675 17669452513916993830402013)
  ·
    refine ⟨6626044692718872686400755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17669452513916993830402013 6626044692718872686400755)
    ·
      refine ⟨9939067039078309029601133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6626044692718872686400755 9939067039078309029601133)
      ·
        refine ⟨3727150139654365886100425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9939067039078309029601133 3727150139654365886100425)
        ·
          refine ⟨2795362604740774414575319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3727150139654365886100425 2795362604740774414575319)
          ·
            refine ⟨4193043907111161621862979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795362604740774414575319 4193043907111161621862979)
            ·
              refine ⟨6289565860666742432794469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4193043907111161621862979 6289565860666742432794469)
              ·
                refine ⟨1179293598875014206148963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6289565860666742432794469 1179293598875014206148963)
                ·
                  refine ⟨1768940398312521309223445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179293598875014206148963 1768940398312521309223445)
                  ·
                    refine ⟨82919081170899436369849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1768940398312521309223445 82919081170899436369849)
                    ·
                      rfl

theorem cell23_484453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_484453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484453 prefixEnd_484453 := by exact prefixLift 484453
  have htrace : WordTrace (prefixWord ++ tailWord_484453) baseStart_484453 baseEnd_484453 := by
    simpa [prefixWord, tailWord_484453, baseEnd_484453] using wordTrace_append hprefix tailTrace_484453
  have hstable : (prefixWord ++ tailWord_484453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484453).length < 2 ^ (prefixWord ++ tailWord_484453).sum := by decide
  have hdescent : baseEnd_484453 < baseStart_484453 := by decide
  rcases family_descends (prefixWord ++ tailWord_484453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484457 : List Nat := [1, 2, 1, 1, 1, 8, 2, 1, 1, 5]
def baseStart_484457 : Nat := 118140960795 + 484457 * 2 ^ 59
def prefixEnd_484457 : Nat := 4983230072969 + 3 ^ 40 * 484457 * 2
def baseEnd_484457 : Nat := 82919765811772097819843

theorem tailTrace_484457 : CollatzResearch.WordTrace tailWord_484457 prefixEnd_484457 82919765811772097819843 := by
  unfold tailWord_484457
  simp only [CollatzResearch.WordTrace]
  refine ⟨17669598405902502513547625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11779732270601668342365083 17669598405902502513547625)
  ·
    refine ⟨13252198804426876885160719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17669598405902502513547625 13252198804426876885160719)
    ·
      refine ⟨19878298206640315327741079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13252198804426876885160719 19878298206640315327741079)
      ·
        refine ⟨29817447309960472991611619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19878298206640315327741079 29817447309960472991611619)
        ·
          refine ⟨44726170964940709487417429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29817447309960472991611619 44726170964940709487417429)
          ·
            refine ⟨524134815995398939305673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 44726170964940709487417429 524134815995398939305673)
            ·
              refine ⟨393101111996549204479255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524134815995398939305673 393101111996549204479255)
              ·
                refine ⟨589651667994823806718883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393101111996549204479255 589651667994823806718883)
                ·
                  refine ⟨884477501992235710078325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589651667994823806718883 884477501992235710078325)
                  ·
                    refine ⟨82919765811772097819843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 884477501992235710078325 82919765811772097819843)
                    ·
                      rfl

theorem cell23_484457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 1, 5].length) (baseStart_484457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484457 prefixEnd_484457 := by exact prefixLift 484457
  have htrace : WordTrace (prefixWord ++ tailWord_484457) baseStart_484457 baseEnd_484457 := by
    simpa [prefixWord, tailWord_484457, baseEnd_484457] using wordTrace_append hprefix tailTrace_484457
  have hstable : (prefixWord ++ tailWord_484457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484457).length < 2 ^ (prefixWord ++ tailWord_484457).sum := by decide
  have hdescent : baseEnd_484457 < baseStart_484457 := by decide
  rcases family_descends (prefixWord ++ tailWord_484457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484460 : List Nat := [2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 4]
def baseStart_484460 : Nat := 118140960795 + 484460 * 2 ^ 59
def prefixEnd_484460 : Nat := 4983230072969 + 3 ^ 40 * 484460 * 2
def baseEnd_484460 : Nat := 248760837877279781722015

theorem tailTrace_484460 : CollatzResearch.WordTrace tailWord_484460 prefixEnd_484460 248760837877279781722015 := by
  unfold tailWord_484460
  simp only [CollatzResearch.WordTrace]
  refine ⟨8834853912445817012953417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11779805216594422683937889 8834853912445817012953417)
  ·
    refine ⟨6626140434334362759715063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8834853912445817012953417 6626140434334362759715063)
    ·
      refine ⟨9939210651501544139572595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6626140434334362759715063 9939210651501544139572595)
      ·
        refine ⟨14908815977252316209358893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9939210651501544139572595 14908815977252316209358893)
        ·
          refine ⟨5590805991469618578509585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14908815977252316209358893 5590805991469618578509585)
          ·
            refine ⟨4193104493602213933882189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5590805991469618578509585 4193104493602213933882189)
            ·
              refine ⟨1572414185100830225205821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4193104493602213933882189 1572414185100830225205821)
              ·
                refine ⟨589655319412811334452183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1572414185100830225205821 589655319412811334452183)
                ·
                  refine ⟨884482979119217001678275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589655319412811334452183 884482979119217001678275)
                  ·
                    refine ⟨1326724468678825502517413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 884482979119217001678275 1326724468678825502517413)
                    ·
                      refine ⟨248760837877279781722015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1326724468678825502517413 248760837877279781722015)
                      ·
                        rfl

theorem cell23_484460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_484460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484460 prefixEnd_484460 := by exact prefixLift 484460
  have htrace : WordTrace (prefixWord ++ tailWord_484460) baseStart_484460 baseEnd_484460 := by
    simpa [prefixWord, tailWord_484460, baseEnd_484460] using wordTrace_append hprefix tailTrace_484460
  have hstable : (prefixWord ++ tailWord_484460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484460).length < 2 ^ (prefixWord ++ tailWord_484460).sum := by decide
  have hdescent : baseEnd_484460 < baseStart_484460 := by decide
  rcases family_descends (prefixWord ++ tailWord_484460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484463 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 5]
def baseStart_484463 : Nat := 118140960795 + 484463 * 2 ^ 59
def prefixEnd_484463 : Nat := 4983230072969 + 3 ^ 40 * 484463 * 2
def baseEnd_484463 : Nat := 248762378319243269984501

theorem tailTrace_484463 : CollatzResearch.WordTrace tailWord_484463 prefixEnd_484463 248762378319243269984501 := by
  unfold tailWord_484463
  simp only [CollatzResearch.WordTrace]
  refine ⟨17669817243880765538266043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11779878162587177025510695 17669817243880765538266043)
  ·
    refine ⟨26504725865821148307399065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17669817243880765538266043 26504725865821148307399065)
    ·
      refine ⟨19878544399365861230549299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26504725865821148307399065 19878544399365861230549299)
      ·
        refine ⟨29817816599048791845823949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19878544399365861230549299 29817816599048791845823949)
        ·
          refine ⟨11181681224643296942183981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29817816599048791845823949 11181681224643296942183981)
          ·
            refine ⟨4193130459241236353318993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11181681224643296942183981 4193130459241236353318993)
            ·
              refine ⟨3144847844430927264989245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4193130459241236353318993 3144847844430927264989245)
              ·
                refine ⟨1179317941661597724370967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3144847844430927264989245 1179317941661597724370967)
                ·
                  refine ⟨1768976912492396586556451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179317941661597724370967 1768976912492396586556451)
                  ·
                    refine ⟨2653465368738594879834677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1768976912492396586556451 2653465368738594879834677)
                    ·
                      refine ⟨248762378319243269984501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2653465368738594879834677 248762378319243269984501)
                      ·
                        rfl

theorem cell23_484463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_484463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484463 prefixEnd_484463 := by exact prefixLift 484463
  have htrace : WordTrace (prefixWord ++ tailWord_484463) baseStart_484463 baseEnd_484463 := by
    simpa [prefixWord, tailWord_484463, baseEnd_484463] using wordTrace_append hprefix tailTrace_484463
  have hstable : (prefixWord ++ tailWord_484463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484463).length < 2 ^ (prefixWord ++ tailWord_484463).sum := by decide
  have hdescent : baseEnd_484463 < baseStart_484463 := by decide
  rcases family_descends (prefixWord ++ tailWord_484463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484494 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2]
def baseStart_484494 : Nat := 118140960795 + 484494 * 2 ^ 59
def prefixEnd_484494 : Nat := 4983230072969 + 3 ^ 40 * 484494 * 2
def baseEnd_484494 : Nat := 248778296219532648696859

theorem tailTrace_484494 : CollatzResearch.WordTrace tailWord_484494 prefixEnd_484494 248778296219532648696859 := by
  unfold tailWord_484494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2208868488346057229080567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11780631937845638555096357 2208868488346057229080567)
  ·
    refine ⟨3313302732519085843620851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2208868488346057229080567 3313302732519085843620851)
    ·
      refine ⟨4969954098778628765431277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3313302732519085843620851 4969954098778628765431277)
      ·
        refine ⟨1863732787041985787036729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4969954098778628765431277 1863732787041985787036729)
        ·
          refine ⟨1397799590281489340277547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1863732787041985787036729 1397799590281489340277547)
          ·
            refine ⟨2096699385422234010416321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397799590281489340277547 2096699385422234010416321)
            ·
              refine ⟨1572524539066675507812241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096699385422234010416321 1572524539066675507812241)
              ·
                refine ⟨1179393404300006630859181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1572524539066675507812241 1179393404300006630859181)
                ·
                  refine ⟨442272526612502486572193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179393404300006630859181 442272526612502486572193)
                  ·
                    refine ⟨331704394959376864929145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 442272526612502486572193 331704394959376864929145)
                    ·
                      refine ⟨248778296219532648696859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 331704394959376864929145 248778296219532648696859)
                      ·
                        rfl

theorem cell23_484494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_484494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484494 prefixEnd_484494 := by exact prefixLift 484494
  have htrace : WordTrace (prefixWord ++ tailWord_484494) baseStart_484494 baseEnd_484494 := by
    simpa [prefixWord, tailWord_484494, baseEnd_484494] using wordTrace_append hprefix tailTrace_484494
  have hstable : (prefixWord ++ tailWord_484494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484494).length < 2 ^ (prefixWord ++ tailWord_484494).sum := by decide
  have hdescent : baseEnd_484494 < baseStart_484494 := by decide
  rcases family_descends (prefixWord ++ tailWord_484494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484534 : List Nat := [5, 1, 3, 2, 1, 1, 2, 8]
def baseStart_484534 : Nat := 118140960795 + 484534 * 2 ^ 59
def prefixEnd_484534 : Nat := 4983230072969 + 3 ^ 40 * 484534 * 2
def baseEnd_484534 : Nat := 9214771683174536748025

theorem tailTrace_484534 : CollatzResearch.WordTrace tailWord_484534 prefixEnd_484534 9214771683174536748025 := by
  unfold tailWord_484534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104525426663971541506291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11781604551082363109400437 1104525426663971541506291)
  ·
    refine ⟨1656788139995957312259437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1104525426663971541506291 1656788139995957312259437)
    ·
      refine ⟨621295552498483992097289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1656788139995957312259437 621295552498483992097289)
      ·
        refine ⟨465971664373862994072967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 621295552498483992097289 465971664373862994072967)
        ·
          refine ⟨698957496560794491109451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465971664373862994072967 698957496560794491109451)
          ·
            refine ⟨1048436244841191736664177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698957496560794491109451 1048436244841191736664177)
            ·
              refine ⟨786327183630893802498133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048436244841191736664177 786327183630893802498133)
              ·
                refine ⟨9214771683174536748025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 786327183630893802498133 9214771683174536748025)
                ·
                  rfl

theorem cell23_484534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_484534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484534 prefixEnd_484534 := by exact prefixLift 484534
  have htrace : WordTrace (prefixWord ++ tailWord_484534) baseStart_484534 baseEnd_484534 := by
    simpa [prefixWord, tailWord_484534, baseEnd_484534] using wordTrace_append hprefix tailTrace_484534
  have hstable : (prefixWord ++ tailWord_484534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484534).length < 2 ^ (prefixWord ++ tailWord_484534).sum := by decide
  have hdescent : baseEnd_484534 < baseStart_484534 := by decide
  rcases family_descends (prefixWord ++ tailWord_484534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484543 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 2, 6]
def baseStart_484543 : Nat := 118140960795 + 484543 * 2 ^ 59
def prefixEnd_484543 : Nat := 4983230072969 + 3 ^ 40 * 484543 * 2
def baseEnd_484543 : Nat := 82934485590534318994711

theorem tailTrace_484543 : CollatzResearch.WordTrace tailWord_484543 prefixEnd_484543 82934485590534318994711 := by
  unfold tailWord_484543
  simp only [CollatzResearch.WordTrace]
  refine ⟨17672735083590939201178283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11781823389060626134118855 17672735083590939201178283)
  ·
    refine ⟨26509102625386408801767425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17672735083590939201178283 26509102625386408801767425)
    ·
      refine ⟨19881826969039806601325569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26509102625386408801767425 19881826969039806601325569)
      ·
        refine ⟨14911370226779854950994177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19881826969039806601325569 14911370226779854950994177)
        ·
          refine ⟨11183527670084891213245633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14911370226779854950994177 11183527670084891213245633)
          ·
            refine ⟨8387645752563668409934225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11183527670084891213245633 8387645752563668409934225)
            ·
              refine ⟨6290734314422751307450669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8387645752563668409934225 6290734314422751307450669)
              ·
                refine ⟨2359025367908531740294001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6290734314422751307450669 2359025367908531740294001)
                ·
                  refine ⟨1769269025931398805220501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2359025367908531740294001 1769269025931398805220501)
                  ·
                    refine ⟨82934485590534318994711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1769269025931398805220501 82934485590534318994711)
                    ·
                      rfl

theorem cell23_484543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 6].length) (baseStart_484543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484543 prefixEnd_484543 := by exact prefixLift 484543
  have htrace : WordTrace (prefixWord ++ tailWord_484543) baseStart_484543 baseEnd_484543 := by
    simpa [prefixWord, tailWord_484543, baseEnd_484543] using wordTrace_append hprefix tailTrace_484543
  have hstable : (prefixWord ++ tailWord_484543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484543).length < 2 ^ (prefixWord ++ tailWord_484543).sum := by decide
  have hdescent : baseEnd_484543 < baseStart_484543 := by decide
  rcases family_descends (prefixWord ++ tailWord_484543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484544 : List Nat := [2, 1, 1, 2, 6, 1, 1, 3, 2, 1, 3]
def baseStart_484544 : Nat := 118140960795 + 484544 * 2 ^ 59
def prefixEnd_484544 : Nat := 4983230072969 + 3 ^ 40 * 484544 * 2
def baseEnd_484544 : Nat := 248803970252257453071629

theorem tailTrace_484544 : CollatzResearch.WordTrace tailWord_484544 prefixEnd_484544 248803970252257453071629 := by
  unfold tailWord_484544
  simp only [CollatzResearch.WordTrace]
  refine ⟨8836385778293658185982343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11781847704391544247976457 8836385778293658185982343)
  ·
    refine ⟨13254578667440487278973515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8836385778293658185982343 13254578667440487278973515)
    ·
      refine ⟨19881868001160730918460273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13254578667440487278973515 19881868001160730918460273)
      ·
        refine ⟨14911401000870548188845205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19881868001160730918460273 14911401000870548188845205)
        ·
          refine ⟨698971921915806946352119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14911401000870548188845205 698971921915806946352119)
          ·
            refine ⟨1048457882873710419528179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698971921915806946352119 1048457882873710419528179)
            ·
              refine ⟨1572686824310565629292269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048457882873710419528179 1572686824310565629292269)
              ·
                refine ⟨589757559116462110984601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1572686824310565629292269 589757559116462110984601)
                ·
                  refine ⟨442318169337346583238451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589757559116462110984601 442318169337346583238451)
                  ·
                    refine ⟨663477254006019874857677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 442318169337346583238451 663477254006019874857677)
                    ·
                      refine ⟨248803970252257453071629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 663477254006019874857677 248803970252257453071629)
                      ·
                        rfl

theorem cell23_484544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_484544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484544 prefixEnd_484544 := by exact prefixLift 484544
  have htrace : WordTrace (prefixWord ++ tailWord_484544) baseStart_484544 baseEnd_484544 := by
    simpa [prefixWord, tailWord_484544, baseEnd_484544] using wordTrace_append hprefix tailTrace_484544
  have hstable : (prefixWord ++ tailWord_484544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484544).length < 2 ^ (prefixWord ++ tailWord_484544).sum := by decide
  have hdescent : baseEnd_484544 < baseStart_484544 := by decide
  rcases family_descends (prefixWord ++ tailWord_484544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484554 : List Nat := [3, 1, 2, 1, 3, 2, 3, 2, 1, 3, 2]
def baseStart_484554 : Nat := 118140960795 + 484554 * 2 ^ 59
def prefixEnd_484554 : Nat := 4983230072969 + 3 ^ 40 * 484554 * 2
def baseEnd_484554 : Nat := 248809105058802413946583

theorem tailTrace_484554 : CollatzResearch.WordTrace tailWord_484554 prefixEnd_484554 248809105058802413946583 := by
  unfold tailWord_484554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4418284071637772019957179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11782090857700725386552477 4418284071637772019957179)
  ·
    refine ⟨6627426107456658029935769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4418284071637772019957179 6627426107456658029935769)
    ·
      refine ⟨4970569580592493522451827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6627426107456658029935769 4970569580592493522451827)
      ·
        refine ⟨7455854370888740283677741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4970569580592493522451827 7455854370888740283677741)
        ·
          refine ⟨2795945389083277606379153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7455854370888740283677741 2795945389083277606379153)
          ·
            refine ⟨2096959041812458204784365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2795945389083277606379153 2096959041812458204784365)
            ·
              refine ⟨786359640679671826794137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2096959041812458204784365 786359640679671826794137)
              ·
                refine ⟨589769730509753870095603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786359640679671826794137 589769730509753870095603)
                ·
                  refine ⟨884654595764630805143405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589769730509753870095603 884654595764630805143405)
                  ·
                    refine ⟨331745473411736551928777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 884654595764630805143405 331745473411736551928777)
                    ·
                      refine ⟨248809105058802413946583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 331745473411736551928777 248809105058802413946583)
                      ·
                        rfl

theorem cell23_484554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_484554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484554 prefixEnd_484554 := by exact prefixLift 484554
  have htrace : WordTrace (prefixWord ++ tailWord_484554) baseStart_484554 baseEnd_484554 := by
    simpa [prefixWord, tailWord_484554, baseEnd_484554] using wordTrace_append hprefix tailTrace_484554
  have hstable : (prefixWord ++ tailWord_484554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484554).length < 2 ^ (prefixWord ++ tailWord_484554).sum := by decide
  have hdescent : baseEnd_484554 < baseStart_484554 := by decide
  rcases family_descends (prefixWord ++ tailWord_484554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484563 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 4]
def baseStart_484563 : Nat := 118140960795 + 484563 * 2 ^ 59
def prefixEnd_484563 : Nat := 4983230072969 + 3 ^ 40 * 484563 * 2
def baseEnd_484563 : Nat := 248813726384692878734041

theorem tailTrace_484563 : CollatzResearch.WordTrace tailWord_484563 prefixEnd_484563 248813726384692878734041 := by
  unfold tailWord_484563
  simp only [CollatzResearch.WordTrace]
  refine ⟨17673464543518482616906343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11782309695678988411270895 17673464543518482616906343)
  ·
    refine ⟨26510196815277723925359515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17673464543518482616906343 26510196815277723925359515)
    ·
      refine ⟨39765295222916585888039273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26510196815277723925359515 39765295222916585888039273)
      ·
        refine ⟨29823971417187439416029455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39765295222916585888039273 29823971417187439416029455)
        ·
          refine ⟨44735957125781159124044183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29823971417187439416029455 44735957125781159124044183)
          ·
            refine ⟨67103935688671738686066275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44735957125781159124044183 67103935688671738686066275)
            ·
              refine ⟨100655903533007608029099413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67103935688671738686066275 100655903533007608029099413)
              ·
                refine ⟨4718245478109731626364035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100655903533007608029099413 4718245478109731626364035)
                ·
                  refine ⟨7077368217164597439546053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4718245478109731626364035 7077368217164597439546053)
                  ·
                    refine ⟨1327006540718362019914885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7077368217164597439546053 1327006540718362019914885)
                    ·
                      refine ⟨248813726384692878734041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1327006540718362019914885 248813726384692878734041)
                      ·
                        rfl

theorem cell23_484563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_484563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484563 prefixEnd_484563 := by exact prefixLift 484563
  have htrace : WordTrace (prefixWord ++ tailWord_484563) baseStart_484563 baseEnd_484563 := by
    simpa [prefixWord, tailWord_484563, baseEnd_484563] using wordTrace_append hprefix tailTrace_484563
  have hstable : (prefixWord ++ tailWord_484563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484563).length < 2 ^ (prefixWord ++ tailWord_484563).sum := by decide
  have hdescent : baseEnd_484563 < baseStart_484563 := by decide
  rcases family_descends (prefixWord ++ tailWord_484563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484567 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 6, 2, 2]
def baseStart_484567 : Nat := 118140960795 + 484567 * 2 ^ 59
def prefixEnd_484567 : Nat := 4983230072969 + 3 ^ 40 * 484567 * 2
def baseEnd_484567 : Nat := 248815780307310863084023

theorem tailTrace_484567 : CollatzResearch.WordTrace tailWord_484567 prefixEnd_484567 248815780307310863084023 := by
  unfold tailWord_484567
  simp only [CollatzResearch.WordTrace]
  refine ⟨17673610435503991300051955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11782406957002660866701303 17673610435503991300051955)
  ·
    refine ⟨26510415653255986950077933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17673610435503991300051955 26510415653255986950077933)
    ·
      refine ⟨9941405869970995106279225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26510415653255986950077933 9941405869970995106279225)
      ·
        refine ⟨7456054402478246329709419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9941405869970995106279225 7456054402478246329709419)
        ·
          refine ⟨11184081603717369494564129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7456054402478246329709419 11184081603717369494564129)
          ·
            refine ⟨8388061202788027120923097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11184081603717369494564129 8388061202788027120923097)
            ·
              refine ⟨6291045902091020340692323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8388061202788027120923097 6291045902091020340692323)
              ·
                refine ⟨9436568853136530511038485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6291045902091020340692323 9436568853136530511038485)
                ·
                  refine ⟨442339164990774867704929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9436568853136530511038485 442339164990774867704929)
                  ·
                    refine ⟨331754373743081150778697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 442339164990774867704929 331754373743081150778697)
                    ·
                      refine ⟨248815780307310863084023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 331754373743081150778697 248815780307310863084023)
                      ·
                        rfl

theorem cell23_484567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_484567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484567 prefixEnd_484567 := by exact prefixLift 484567
  have htrace : WordTrace (prefixWord ++ tailWord_484567) baseStart_484567 baseEnd_484567 := by
    simpa [prefixWord, tailWord_484567, baseEnd_484567] using wordTrace_append hprefix tailTrace_484567
  have hstable : (prefixWord ++ tailWord_484567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484567).length < 2 ^ (prefixWord ++ tailWord_484567).sum := by decide
  have hdescent : baseEnd_484567 < baseStart_484567 := by decide
  rcases family_descends (prefixWord ++ tailWord_484567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484593 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_484593 : Nat := 118140960795 + 484593 * 2 ^ 59
def prefixEnd_484593 : Nat := 4983230072969 + 3 ^ 40 * 484593 * 2
def baseEnd_484593 : Nat := 248829130804327761358903

theorem tailTrace_484593 : CollatzResearch.WordTrace tailWord_484593 prefixEnd_484593 248829130804327761358903 := by
  unfold tailWord_484593
  simp only [CollatzResearch.WordTrace]
  refine ⟨17674558733409797740498433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11783039155606531826998955 17674558733409797740498433)
  ·
    refine ⟨13255919050057348305373825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17674558733409797740498433 13255919050057348305373825)
    ·
      refine ⟨9941939287543011229030369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13255919050057348305373825 9941939287543011229030369)
      ·
        refine ⟨7456454465657258421772777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9941939287543011229030369 7456454465657258421772777)
        ·
          refine ⟨5592340849242943816329583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7456454465657258421772777 5592340849242943816329583)
          ·
            refine ⟨8388511273864415724494375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5592340849242943816329583 8388511273864415724494375)
            ·
              refine ⟨12582766910796623586741563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8388511273864415724494375 12582766910796623586741563)
              ·
                refine ⟨18874150366194935380112345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12582766910796623586741563 18874150366194935380112345)
                ·
                  refine ⟨14155612774646201535084259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18874150366194935380112345 14155612774646201535084259)
                  ·
                    refine ⟨21233419161969302302626389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14155612774646201535084259 21233419161969302302626389)
                    ·
                      refine ⟨248829130804327761358903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 21233419161969302302626389 248829130804327761358903)
                      ·
                        rfl

theorem cell23_484593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_484593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484593 prefixEnd_484593 := by exact prefixLift 484593
  have htrace : WordTrace (prefixWord ++ tailWord_484593) baseStart_484593 baseEnd_484593 := by
    simpa [prefixWord, tailWord_484593, baseEnd_484593] using wordTrace_append hprefix tailTrace_484593
  have hstable : (prefixWord ++ tailWord_484593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484593).length < 2 ^ (prefixWord ++ tailWord_484593).sum := by decide
  have hdescent : baseEnd_484593 < baseStart_484593 := by decide
  rcases family_descends (prefixWord ++ tailWord_484593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484620 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 1, 7]
def baseStart_484620 : Nat := 118140960795 + 484620 * 2 ^ 59
def prefixEnd_484620 : Nat := 4983230072969 + 3 ^ 40 * 484620 * 2
def baseEnd_484620 : Nat := 82947664927333051907093

theorem tailTrace_484620 : CollatzResearch.WordTrace tailWord_484620 prefixEnd_484620 82947664927333051907093 := by
  unfold tailWord_484620
  simp only [CollatzResearch.WordTrace]
  refine ⟨8837771752155990675865657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11783695669541320901154209 8837771752155990675865657)
  ·
    refine ⟨6628328814116993006899243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8837771752155990675865657 6628328814116993006899243)
    ·
      refine ⟨9942493221175489510348865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6628328814116993006899243 9942493221175489510348865)
      ·
        refine ⟨7456869915881617132761649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9942493221175489510348865 7456869915881617132761649)
        ·
          refine ⟨5592652436911212849571237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7456869915881617132761649 5592652436911212849571237)
          ·
            refine ⟨1048622331920852409294607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5592652436911212849571237 1048622331920852409294607)
            ·
              refine ⟨1572933497881278613941911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048622331920852409294607 1572933497881278613941911)
              ·
                refine ⟨2359400246821917920912867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572933497881278613941911 2359400246821917920912867)
                ·
                  refine ⟨3539100370232876881369301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359400246821917920912867 3539100370232876881369301)
                  ·
                    refine ⟨82947664927333051907093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3539100370232876881369301 82947664927333051907093)
                    ·
                      rfl

theorem cell23_484620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_484620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484620 prefixEnd_484620 := by exact prefixLift 484620
  have htrace : WordTrace (prefixWord ++ tailWord_484620) baseStart_484620 baseEnd_484620 := by
    simpa [prefixWord, tailWord_484620, baseEnd_484620] using wordTrace_append hprefix tailTrace_484620
  have hstable : (prefixWord ++ tailWord_484620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484620).length < 2 ^ (prefixWord ++ tailWord_484620).sum := by decide
  have hdescent : baseEnd_484620 < baseStart_484620 := by decide
  rcases family_descends (prefixWord ++ tailWord_484620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484633 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 3, 10]
def baseStart_484633 : Nat := 118140960795 + 484633 * 2 ^ 59
def prefixEnd_484633 : Nat := 4983230072969 + 3 ^ 40 * 484633 * 2
def baseEnd_484633 : Nat := 82949890010169201619573

theorem tailTrace_484633 : CollatzResearch.WordTrace tailWord_484633 prefixEnd_484633 82949890010169201619573 := by
  unfold tailWord_484633
  simp only [CollatzResearch.WordTrace]
  refine ⟨17676017653264884571954553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11784011768843256381303035 17676017653264884571954553)
  ·
    refine ⟨13257013239948663428965915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17676017653264884571954553 13257013239948663428965915)
    ·
      refine ⟨19885519859922995143448873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13257013239948663428965915 19885519859922995143448873)
      ·
        refine ⟨14914139894942246357586655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19885519859922995143448873 14914139894942246357586655)
        ·
          refine ⟨22371209842413369536379983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14914139894942246357586655 22371209842413369536379983)
          ·
            refine ⟨33556814763620054304569975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22371209842413369536379983 33556814763620054304569975)
            ·
              refine ⟨50335222145430081456854963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33556814763620054304569975 50335222145430081456854963)
              ·
                refine ⟨75502833218145122185282445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50335222145430081456854963 75502833218145122185282445)
                ·
                  refine ⟨28313562456804420819480917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75502833218145122185282445 28313562456804420819480917)
                  ·
                    refine ⟨82949890010169201619573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 28313562456804420819480917 82949890010169201619573)
                    ·
                      rfl

theorem cell23_484633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_484633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484633 prefixEnd_484633 := by exact prefixLift 484633
  have htrace : WordTrace (prefixWord ++ tailWord_484633) baseStart_484633 baseEnd_484633 := by
    simpa [prefixWord, tailWord_484633, baseEnd_484633] using wordTrace_append hprefix tailTrace_484633
  have hstable : (prefixWord ++ tailWord_484633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484633).length < 2 ^ (prefixWord ++ tailWord_484633).sum := by decide
  have hdescent : baseEnd_484633 < baseStart_484633 := by decide
  rcases family_descends (prefixWord ++ tailWord_484633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484714 : List Nat := [3, 1, 3, 3, 2, 1, 1, 3, 6]
def baseStart_484714 : Nat := 118140960795 + 484714 * 2 ^ 59
def prefixEnd_484714 : Nat := 4983230072969 + 3 ^ 40 * 484714 * 2
def baseEnd_484714 : Nat := 27654584662613531993983

theorem tailTrace_484714 : CollatzResearch.WordTrace tailWord_484714 prefixEnd_484714 27654584662613531993983 := by
  unfold tailWord_484714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4419742991492858851413299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11785981310647623603768797 4419742991492858851413299)
  ·
    refine ⟨6629614487239288277119949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4419742991492858851413299 6629614487239288277119949)
    ·
      refine ⟨2486105432714733103919981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6629614487239288277119949 2486105432714733103919981)
      ·
        refine ⟨932289537268024913969993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2486105432714733103919981 932289537268024913969993)
        ·
          refine ⟨699217152951018685477495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932289537268024913969993 699217152951018685477495)
          ·
            refine ⟨1048825729426528028216243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699217152951018685477495 1048825729426528028216243)
            ·
              refine ⟨1573238594139792042324365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048825729426528028216243 1573238594139792042324365)
              ·
                refine ⟨589964472802422015871637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1573238594139792042324365 589964472802422015871637)
                ·
                  refine ⟨27654584662613531993983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 589964472802422015871637 27654584662613531993983)
                  ·
                    rfl

theorem cell23_484714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 6].length) (baseStart_484714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484714 prefixEnd_484714 := by exact prefixLift 484714
  have htrace : WordTrace (prefixWord ++ tailWord_484714) baseStart_484714 baseEnd_484714 := by
    simpa [prefixWord, tailWord_484714, baseEnd_484714] using wordTrace_append hprefix tailTrace_484714
  have hstable : (prefixWord ++ tailWord_484714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484714).length < 2 ^ (prefixWord ++ tailWord_484714).sum := by decide
  have hdescent : baseEnd_484714 < baseStart_484714 := by decide
  rcases family_descends (prefixWord ++ tailWord_484714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484730 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_484730 : Nat := 118140960795 + 484730 * 2 ^ 59
def prefixEnd_484730 : Nat := 4983230072969 + 3 ^ 40 * 484730 * 2
def baseEnd_484730 : Nat := 248899477653993725345773

theorem tailTrace_484730 : CollatzResearch.WordTrace tailWord_484730 prefixEnd_484730 248899477653993725345773 := by
  unfold tailWord_484730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4419888883478367534558911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11786370355942313425490429 4419888883478367534558911)
  ·
    refine ⟨6629833325217551301838367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4419888883478367534558911 6629833325217551301838367)
    ·
      refine ⟨9944749987826326952757551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6629833325217551301838367 9944749987826326952757551)
      ·
        refine ⟨14917124981739490429136327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9944749987826326952757551 14917124981739490429136327)
        ·
          refine ⟨22375687472609235643704491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14917124981739490429136327 22375687472609235643704491)
          ·
            refine ⟨33563531208913853465556737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22375687472609235643704491 33563531208913853465556737)
            ·
              refine ⟨25172648406685390099167553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33563531208913853465556737 25172648406685390099167553)
              ·
                refine ⟨18879486305014042574375665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25172648406685390099167553 18879486305014042574375665)
                ·
                  refine ⟨14159614728760531930781749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18879486305014042574375665 14159614728760531930781749)
                  ·
                    refine ⟨1327463880821299868510789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14159614728760531930781749 1327463880821299868510789)
                    ·
                      refine ⟨248899477653993725345773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1327463880821299868510789 248899477653993725345773)
                      ·
                        rfl

theorem cell23_484730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_484730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484730 prefixEnd_484730 := by exact prefixLift 484730
  have htrace : WordTrace (prefixWord ++ tailWord_484730) baseStart_484730 baseEnd_484730 := by
    simpa [prefixWord, tailWord_484730, baseEnd_484730] using wordTrace_append hprefix tailTrace_484730
  have hstable : (prefixWord ++ tailWord_484730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484730).length < 2 ^ (prefixWord ++ tailWord_484730).sum := by decide
  have hdescent : baseEnd_484730 < baseStart_484730 := by decide
  rcases family_descends (prefixWord ++ tailWord_484730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484757 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 4, 4]
def baseStart_484757 : Nat := 118140960795 + 484757 * 2 ^ 59
def prefixEnd_484757 : Nat := 4983230072969 + 3 ^ 40 * 484757 * 2
def baseEnd_484757 : Nat := 82971113877221706569383

theorem tailTrace_484757 : CollatzResearch.WordTrace tailWord_484757 prefixEnd_484757 82971113877221706569383 := by
  unfold tailWord_484757
  simp only [CollatzResearch.WordTrace]
  refine ⟨17680540304815653749468525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11787026869877102499645683 17680540304815653749468525)
  ·
    refine ⟨6630202614305870156050697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17680540304815653749468525 6630202614305870156050697)
    ·
      refine ⟨4972651960729402617038023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6630202614305870156050697 4972651960729402617038023)
      ·
        refine ⟨7458977941094103925557035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4972651960729402617038023 7458977941094103925557035)
        ·
          refine ⟨11188466911641155888335553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7458977941094103925557035 11188466911641155888335553)
          ·
            refine ⟨8391350183730866916251665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11188466911641155888335553 8391350183730866916251665)
            ·
              refine ⟨6293512637798150187188749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8391350183730866916251665 6293512637798150187188749)
              ·
                refine ⟨2360067239174306320195781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6293512637798150187188749 2360067239174306320195781)
                ·
                  refine ⟨442512607345182435036709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2360067239174306320195781 442512607345182435036709)
                  ·
                    refine ⟨82971113877221706569383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 442512607345182435036709 82971113877221706569383)
                    ·
                      rfl

theorem cell23_484757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_484757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484757 prefixEnd_484757 := by exact prefixLift 484757
  have htrace : WordTrace (prefixWord ++ tailWord_484757) baseStart_484757 baseEnd_484757 := by
    simpa [prefixWord, tailWord_484757, baseEnd_484757] using wordTrace_append hprefix tailTrace_484757
  have hstable : (prefixWord ++ tailWord_484757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484757).length < 2 ^ (prefixWord ++ tailWord_484757).sum := by decide
  have hdescent : baseEnd_484757 < baseStart_484757 := by decide
  rcases family_descends (prefixWord ++ tailWord_484757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484824 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 5, 3, 2]
def baseStart_484824 : Nat := 118140960795 + 484824 * 2 ^ 59
def prefixEnd_484824 : Nat := 4983230072969 + 3 ^ 40 * 484824 * 2
def baseEnd_484824 : Nat := 248947744835516357570341

theorem tailTrace_484824 : CollatzResearch.WordTrace tailWord_484824 prefixEnd_484824 248947744835516357570341 := by
  unfold tailWord_484824
  simp only [CollatzResearch.WordTrace]
  refine ⟨8841491997786462096078763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11788655997048616128105017 8841491997786462096078763)
  ·
    refine ⟨13262237996679693144118145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8841491997786462096078763 13262237996679693144118145)
    ·
      refine ⟨9946678497509769858088609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13262237996679693144118145 9946678497509769858088609)
      ·
        refine ⟨7460008873132327393566457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9946678497509769858088609 7460008873132327393566457)
        ·
          refine ⟨5595006654849245545174843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7460008873132327393566457 5595006654849245545174843)
          ·
            refine ⟨8392509982273868317762265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5595006654849245545174843 8392509982273868317762265)
            ·
              refine ⟨6294382486705401238321699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8392509982273868317762265 6294382486705401238321699)
              ·
                refine ⟨9441573730058101857482549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6294382486705401238321699 9441573730058101857482549)
                ·
                  refine ⟨885147537192947049138989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9441573730058101857482549 885147537192947049138989)
                  ·
                    refine ⟨331930326447355143427121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 885147537192947049138989 331930326447355143427121)
                    ·
                      refine ⟨248947744835516357570341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 331930326447355143427121 248947744835516357570341)
                      ·
                        rfl

theorem cell23_484824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_484824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484824 prefixEnd_484824 := by exact prefixLift 484824
  have htrace : WordTrace (prefixWord ++ tailWord_484824) baseStart_484824 baseEnd_484824 := by
    simpa [prefixWord, tailWord_484824, baseEnd_484824] using wordTrace_append hprefix tailTrace_484824
  have hstable : (prefixWord ++ tailWord_484824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484824).length < 2 ^ (prefixWord ++ tailWord_484824).sum := by decide
  have hdescent : baseEnd_484824 < baseStart_484824 := by decide
  rcases family_descends (prefixWord ++ tailWord_484824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484857 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 1, 6, 3]
def baseStart_484857 : Nat := 118140960795 + 484857 * 2 ^ 59
def prefixEnd_484857 : Nat := 4983230072969 + 3 ^ 40 * 484857 * 2
def baseEnd_484857 : Nat := 248964689697114728457689

theorem tailTrace_484857 : CollatzResearch.WordTrace tailWord_484857 prefixEnd_484857 248964689697114728457689 := by
  unfold tailWord_484857
  simp only [CollatzResearch.WordTrace]
  refine ⟨17684187604453370828108825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11789458402968913885405883 17684187604453370828108825)
  ·
    refine ⟨13263140703340028121081619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17684187604453370828108825 13263140703340028121081619)
    ·
      refine ⟨19894711055010042181622429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13263140703340028121081619 19894711055010042181622429)
      ·
        refine ⟨7460516645628765818108411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19894711055010042181622429 7460516645628765818108411)
        ·
          refine ⟨11190774968443148727162617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7460516645628765818108411 11190774968443148727162617)
          ·
            refine ⟨8393081226332361545371963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11190774968443148727162617 8393081226332361545371963)
            ·
              refine ⟨12589621839498542318057945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8393081226332361545371963 12589621839498542318057945)
              ·
                refine ⟨9442216379623906738543459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12589621839498542318057945 9442216379623906738543459)
                ·
                  refine ⟨14163324569435860107815189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9442216379623906738543459 14163324569435860107815189)
                  ·
                    refine ⟨663905839192305942553837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14163324569435860107815189 663905839192305942553837)
                    ·
                      refine ⟨248964689697114728457689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 663905839192305942553837 248964689697114728457689)
                      ·
                        rfl

theorem cell23_484857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_484857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484857 prefixEnd_484857 := by exact prefixLift 484857
  have htrace : WordTrace (prefixWord ++ tailWord_484857) baseStart_484857 baseEnd_484857 := by
    simpa [prefixWord, tailWord_484857, baseEnd_484857] using wordTrace_append hprefix tailTrace_484857
  have hstable : (prefixWord ++ tailWord_484857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484857).length < 2 ^ (prefixWord ++ tailWord_484857).sum := by decide
  have hdescent : baseEnd_484857 < baseStart_484857 := by decide
  rcases family_descends (prefixWord ++ tailWord_484857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484867 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 4]
def baseStart_484867 : Nat := 118140960795 + 484867 * 2 ^ 59
def prefixEnd_484867 : Nat := 4983230072969 + 3 ^ 40 * 484867 * 2
def baseEnd_484867 : Nat := 248969824503659689332643

theorem tailTrace_484867 : CollatzResearch.WordTrace tailWord_484867 prefixEnd_484867 248969824503659689332643 := by
  unfold tailWord_484867
  simp only [CollatzResearch.WordTrace]
  refine ⟨17684552334417142535972855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11789701556278095023981903 17684552334417142535972855)
  ·
    refine ⟨26526828501625713803959283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17684552334417142535972855 26526828501625713803959283)
    ·
      refine ⟨39790242752438570705938925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26526828501625713803959283 39790242752438570705938925)
      ·
        refine ⟨14921341032164464014727097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39790242752438570705938925 14921341032164464014727097)
        ·
          refine ⟨11191005774123348011045323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14921341032164464014727097 11191005774123348011045323)
          ·
            refine ⟨16786508661185022016567985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11191005774123348011045323 16786508661185022016567985)
            ·
              refine ⟨12589881495888766512425989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16786508661185022016567985 12589881495888766512425989)
              ·
                refine ⟨2360602780479143721079873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12589881495888766512425989 2360602780479143721079873)
                ·
                  refine ⟨1770452085359357790809905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2360602780479143721079873 1770452085359357790809905)
                  ·
                    refine ⟨1327839064019518343107429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1770452085359357790809905 1327839064019518343107429)
                    ·
                      refine ⟨248969824503659689332643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1327839064019518343107429 248969824503659689332643)
                      ·
                        rfl

theorem cell23_484867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_484867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484867 prefixEnd_484867 := by exact prefixLift 484867
  have htrace : WordTrace (prefixWord ++ tailWord_484867) baseStart_484867 baseEnd_484867 := by
    simpa [prefixWord, tailWord_484867, baseEnd_484867] using wordTrace_append hprefix tailTrace_484867
  have hstable : (prefixWord ++ tailWord_484867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484867).length < 2 ^ (prefixWord ++ tailWord_484867).sum := by decide
  have hdescent : baseEnd_484867 < baseStart_484867 := by decide
  rcases family_descends (prefixWord ++ tailWord_484867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484987 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 8]
def baseStart_484987 : Nat := 118140960795 + 484987 * 2 ^ 59
def prefixEnd_484987 : Nat := 4983230072969 + 3 ^ 40 * 484987 * 2
def baseEnd_484987 : Nat := 249031442182199219832091

theorem tailTrace_484987 : CollatzResearch.WordTrace tailWord_484987 prefixEnd_484987 249031442182199219832091 := by
  unfold tailWord_484987
  simp only [CollatzResearch.WordTrace]
  refine ⟨17688929093982403030341215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11792619395988268686894143 17688929093982403030341215)
  ·
    refine ⟨26533393640973604545511823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17688929093982403030341215 26533393640973604545511823)
    ·
      refine ⟨39800090461460406818267735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26533393640973604545511823 39800090461460406818267735)
      ·
        refine ⟨59700135692190610227401603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39800090461460406818267735 59700135692190610227401603)
        ·
          refine ⟨89550203538285915341102405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59700135692190610227401603 89550203538285915341102405)
          ·
            refine ⟨16790663163428609126456701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89550203538285915341102405 16790663163428609126456701)
            ·
              refine ⟨6296498686285728422421263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16790663163428609126456701 6296498686285728422421263)
              ·
                refine ⟨9444748029428592633631895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6296498686285728422421263 9444748029428592633631895)
                ·
                  refine ⟨14167122044142888950447843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9444748029428592633631895 14167122044142888950447843)
                  ·
                    refine ⟨21250683066214333425671765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14167122044142888950447843 21250683066214333425671765)
                    ·
                      refine ⟨249031442182199219832091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 21250683066214333425671765 249031442182199219832091)
                      ·
                        rfl

theorem cell23_484987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 8].length) (baseStart_484987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_484987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_484987 prefixEnd_484987 := by exact prefixLift 484987
  have htrace : WordTrace (prefixWord ++ tailWord_484987) baseStart_484987 baseEnd_484987 := by
    simpa [prefixWord, tailWord_484987, baseEnd_484987] using wordTrace_append hprefix tailTrace_484987
  have hstable : (prefixWord ++ tailWord_484987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484987).length < 2 ^ (prefixWord ++ tailWord_484987).sum := by decide
  have hdescent : baseEnd_484987 < baseStart_484987 := by decide
  rcases family_descends (prefixWord ++ tailWord_484987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485022 : List Nat := [4, 3, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_485022 : Nat := 118140960795 + 485022 * 2 ^ 59
def prefixEnd_485022 : Nat := 4983230072969 + 3 ^ 40 * 485022 * 2
def baseEnd_485022 : Nat := 83016471335035527631477

theorem tailTrace_485022 : CollatzResearch.WordTrace tailWord_485022 prefixEnd_485022 83016471335035527631477 := by
  unfold tailWord_485022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2211275706106950500983165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11793470432570402671910213 2211275706106950500983165)
  ·
    refine ⟨829228389790106437868687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2211275706106950500983165 829228389790106437868687)
    ·
      refine ⟨1243842584685159656803031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829228389790106437868687 1243842584685159656803031)
      ·
        refine ⟨1865763877027739485204547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243842584685159656803031 1865763877027739485204547)
        ·
          refine ⟨2798645815541609227806821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865763877027739485204547 2798645815541609227806821)
          ·
            refine ⟨524746090414051730213779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2798645815541609227806821 524746090414051730213779)
            ·
              refine ⟨787119135621077595320669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524746090414051730213779 787119135621077595320669)
              ·
                refine ⟨295169675857904098245251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 787119135621077595320669 295169675857904098245251)
                ·
                  refine ⟨442754513786856147367877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295169675857904098245251 442754513786856147367877)
                  ·
                    refine ⟨83016471335035527631477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 442754513786856147367877 83016471335035527631477)
                    ·
                      rfl

theorem cell23_485022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_485022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485022 prefixEnd_485022 := by exact prefixLift 485022
  have htrace : WordTrace (prefixWord ++ tailWord_485022) baseStart_485022 baseEnd_485022 := by
    simpa [prefixWord, tailWord_485022, baseEnd_485022] using wordTrace_append hprefix tailTrace_485022
  have hstable : (prefixWord ++ tailWord_485022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485022).length < 2 ^ (prefixWord ++ tailWord_485022).sum := by decide
  have hdescent : baseEnd_485022 < baseStart_485022 := by decide
  rcases family_descends (prefixWord ++ tailWord_485022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485032 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_485032 : Nat := 118140960795 + 485032 * 2 ^ 59
def prefixEnd_485032 : Nat := 4983230072969 + 3 ^ 40 * 485032 * 2
def baseEnd_485032 : Nat := 249054548811651543769385

theorem tailTrace_485032 : CollatzResearch.WordTrace tailWord_485032 prefixEnd_485032 249054548811651543769385 := by
  unfold tailWord_485032
  simp only [CollatzResearch.WordTrace]
  refine ⟨8845285189409687857864675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11793713585879583810486233 8845285189409687857864675)
  ·
    refine ⟨13267927784114531786797013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8845285189409687857864675 13267927784114531786797013)
    ·
      refine ⟨310967057440184338753055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13267927784114531786797013 310967057440184338753055)
      ·
        refine ⟨466450586160276508129583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310967057440184338753055 466450586160276508129583)
        ·
          refine ⟨699675879240414762194375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466450586160276508129583 699675879240414762194375)
          ·
            refine ⟨1049513818860622143291563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699675879240414762194375 1049513818860622143291563)
            ·
              refine ⟨1574270728290933214937345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049513818860622143291563 1574270728290933214937345)
              ·
                refine ⟨1180703046218199911203009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574270728290933214937345 1180703046218199911203009)
                ·
                  refine ⟨885527284663649933402257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1180703046218199911203009 885527284663649933402257)
                  ·
                    refine ⟨664145463497737450051693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 885527284663649933402257 664145463497737450051693)
                    ·
                      refine ⟨249054548811651543769385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 664145463497737450051693 249054548811651543769385)
                      ·
                        rfl

theorem cell23_485032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_485032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485032 prefixEnd_485032 := by exact prefixLift 485032
  have htrace : WordTrace (prefixWord ++ tailWord_485032) baseStart_485032 baseEnd_485032 := by
    simpa [prefixWord, tailWord_485032, baseEnd_485032] using wordTrace_append hprefix tailTrace_485032
  have hstable : (prefixWord ++ tailWord_485032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485032).length < 2 ^ (prefixWord ++ tailWord_485032).sum := by decide
  have hdescent : baseEnd_485032 < baseStart_485032 := by decide
  rcases family_descends (prefixWord ++ tailWord_485032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485061 : List Nat := [1, 3, 1, 1, 1, 1, 2, 7, 2, 4]
def baseStart_485061 : Nat := 118140960795 + 485061 * 2 ^ 59
def prefixEnd_485061 : Nat := 4983230072969 + 3 ^ 40 * 485061 * 2
def baseEnd_485061 : Nat := 83023146583543976768917

theorem tailTrace_485061 : CollatzResearch.WordTrace tailWord_485061 prefixEnd_485061 83023146583543976768917 := by
  unfold tailWord_485061
  simp only [CollatzResearch.WordTrace]
  refine ⟨17691628095714313668535037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11794418730476209112356691 17691628095714313668535037)
  ·
    refine ⟨6634360535892867625700639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17691628095714313668535037 6634360535892867625700639)
    ·
      refine ⟨9951540803839301438550959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6634360535892867625700639 9951540803839301438550959)
      ·
        refine ⟨14927311205758952157826439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9951540803839301438550959 14927311205758952157826439)
        ·
          refine ⟨22390966808638428236739659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14927311205758952157826439 22390966808638428236739659)
          ·
            refine ⟨33586450212957642355109489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22390966808638428236739659 33586450212957642355109489)
            ·
              refine ⟨25189837659718231766332117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33586450212957642355109489 25189837659718231766332117)
              ·
                refine ⟨590386820149646057023409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25189837659718231766332117 590386820149646057023409)
                ·
                  refine ⟨442790115112234542767557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590386820149646057023409 442790115112234542767557)
                  ·
                    refine ⟨83023146583543976768917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 442790115112234542767557 83023146583543976768917)
                    ·
                      rfl

theorem cell23_485061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_485061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485061 prefixEnd_485061 := by exact prefixLift 485061
  have htrace : WordTrace (prefixWord ++ tailWord_485061) baseStart_485061 baseEnd_485061 := by
    simpa [prefixWord, tailWord_485061, baseEnd_485061] using wordTrace_append hprefix tailTrace_485061
  have hstable : (prefixWord ++ tailWord_485061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485061).length < 2 ^ (prefixWord ++ tailWord_485061).sum := by decide
  have hdescent : baseEnd_485061 < baseStart_485061 := by decide
  rcases family_descends (prefixWord ++ tailWord_485061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485064 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_485064 : Nat := 118140960795 + 485064 * 2 ^ 59
def prefixEnd_485064 : Nat := 4983230072969 + 3 ^ 40 * 485064 * 2
def baseEnd_485064 : Nat := 249070980192595418569237

theorem tailTrace_485064 : CollatzResearch.WordTrace tailWord_485064 prefixEnd_485064 249070980192595418569237 := by
  unfold tailWord_485064
  simp only [CollatzResearch.WordTrace]
  refine ⟨8845868757351722590447123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11794491676468963453929497 8845868757351722590447123)
  ·
    refine ⟨13268803136027583885670685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8845868757351722590447123 13268803136027583885670685)
    ·
      refine ⟨4975801176010343957126507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13268803136027583885670685 4975801176010343957126507)
      ·
        refine ⟨7463701764015515935689761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4975801176010343957126507 7463701764015515935689761)
        ·
          refine ⟨5597776323011636951767321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7463701764015515935689761 5597776323011636951767321)
          ·
            refine ⟨4198332242258727713825491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5597776323011636951767321 4198332242258727713825491)
            ·
              refine ⟨6297498363388091570738237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4198332242258727713825491 6297498363388091570738237)
              ·
                refine ⟨2361561886270534339026839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6297498363388091570738237 2361561886270534339026839)
                ·
                  refine ⟨3542342829405801508540259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361561886270534339026839 3542342829405801508540259)
                  ·
                    refine ⟨5313514244108702262810389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3542342829405801508540259 5313514244108702262810389)
                    ·
                      refine ⟨249070980192595418569237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5313514244108702262810389 249070980192595418569237)
                      ·
                        rfl

theorem cell23_485064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_485064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485064 prefixEnd_485064 := by exact prefixLift 485064
  have htrace : WordTrace (prefixWord ++ tailWord_485064) baseStart_485064 baseEnd_485064 := by
    simpa [prefixWord, tailWord_485064, baseEnd_485064] using wordTrace_append hprefix tailTrace_485064
  have hstable : (prefixWord ++ tailWord_485064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485064).length < 2 ^ (prefixWord ++ tailWord_485064).sum := by decide
  have hdescent : baseEnd_485064 < baseStart_485064 := by decide
  rcases family_descends (prefixWord ++ tailWord_485064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485068 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 3, 1, 4]
def baseStart_485068 : Nat := 118140960795 + 485068 * 2 ^ 59
def prefixEnd_485068 : Nat := 4983230072969 + 3 ^ 40 * 485068 * 2
def baseEnd_485068 : Nat := 249073034115213402919219

theorem tailTrace_485068 : CollatzResearch.WordTrace tailWord_485068 prefixEnd_485068 249073034115213402919219 := by
  unfold tailWord_485068
  simp only [CollatzResearch.WordTrace]
  refine ⟨8845941703344476932019929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11794588937792635909359905 8845941703344476932019929)
  ·
    refine ⟨6634456277508357699014947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8845941703344476932019929 6634456277508357699014947)
    ·
      refine ⟨9951684416262536548522421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6634456277508357699014947 9951684416262536548522421)
      ·
        refine ⟨932970414024612801423977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9951684416262536548522421 932970414024612801423977)
        ·
          refine ⟨699727810518459601067983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932970414024612801423977 699727810518459601067983)
          ·
            refine ⟨1049591715777689401601975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699727810518459601067983 1049591715777689401601975)
            ·
              refine ⟨1574387573666534102402963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049591715777689401601975 1574387573666534102402963)
              ·
                refine ⟨2361581360499801153604445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574387573666534102402963 2361581360499801153604445)
                ·
                  refine ⟨885593010187425432601667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2361581360499801153604445 885593010187425432601667)
                  ·
                    refine ⟨1328389515281138148902501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 885593010187425432601667 1328389515281138148902501)
                    ·
                      refine ⟨249073034115213402919219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1328389515281138148902501 249073034115213402919219)
                      ·
                        rfl

theorem cell23_485068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_485068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485068 prefixEnd_485068 := by exact prefixLift 485068
  have htrace : WordTrace (prefixWord ++ tailWord_485068) baseStart_485068 baseEnd_485068 := by
    simpa [prefixWord, tailWord_485068, baseEnd_485068] using wordTrace_append hprefix tailTrace_485068
  have hstable : (prefixWord ++ tailWord_485068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485068).length < 2 ^ (prefixWord ++ tailWord_485068).sum := by decide
  have hdescent : baseEnd_485068 < baseStart_485068 := by decide
  rcases family_descends (prefixWord ++ tailWord_485068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485081 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 1, 2, 4]
def baseStart_485081 : Nat := 118140960795 + 485081 * 2 ^ 59
def prefixEnd_485081 : Nat := 4983230072969 + 3 ^ 40 * 485081 * 2
def baseEnd_485081 : Nat := 249079709363721852056659

theorem tailTrace_485081 : CollatzResearch.WordTrace tailWord_485081 prefixEnd_485081 249079709363721852056659 := by
  unfold tailWord_485081
  simp only [CollatzResearch.WordTrace]
  refine ⟨17692357555641857084263097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11794905037094571389508731 17692357555641857084263097)
  ·
    refine ⟨13269268166731392813197323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17692357555641857084263097 13269268166731392813197323)
    ·
      refine ⟨19903902250097089219795985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13269268166731392813197323 19903902250097089219795985)
      ·
        refine ⟨14927926687572816914846989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19903902250097089219795985 14927926687572816914846989)
        ·
          refine ⟨5597972507839806343067621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14927926687572816914846989 5597972507839806343067621)
          ·
            refine ⟨1049619845219963689325179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5597972507839806343067621 1049619845219963689325179)
            ·
              refine ⟨1574429767829945533987769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049619845219963689325179 1574429767829945533987769)
              ·
                refine ⟨1180822325872459150490827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574429767829945533987769 1180822325872459150490827)
                ·
                  refine ⟨1771233488808688725736241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180822325872459150490827 1771233488808688725736241)
                  ·
                    refine ⟨1328425116606516544302181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1771233488808688725736241 1328425116606516544302181)
                    ·
                      refine ⟨249079709363721852056659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1328425116606516544302181 249079709363721852056659)
                      ·
                        rfl

theorem cell23_485081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_485081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485081 prefixEnd_485081 := by exact prefixLift 485081
  have htrace : WordTrace (prefixWord ++ tailWord_485081) baseStart_485081 baseEnd_485081 := by
    simpa [prefixWord, tailWord_485081, baseEnd_485081] using wordTrace_append hprefix tailTrace_485081
  have hstable : (prefixWord ++ tailWord_485081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485081).length < 2 ^ (prefixWord ++ tailWord_485081).sum := by decide
  have hdescent : baseEnd_485081 < baseStart_485081 := by decide
  rcases family_descends (prefixWord ++ tailWord_485081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485091 : List Nat := [1, 1, 1, 7, 3, 10]
def baseStart_485091 : Nat := 118140960795 + 485091 * 2 ^ 59
def prefixEnd_485091 : Nat := 4983230072969 + 3 ^ 40 * 485091 * 2
def baseEnd_485091 : Nat := 1025040510988752316591

theorem tailTrace_485091 : CollatzResearch.WordTrace tailWord_485091 prefixEnd_485091 1025040510988752316591 := by
  unfold tailWord_485091
  simp only [CollatzResearch.WordTrace]
  refine ⟨17692722285605628792127127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11795148190403752528084751 17692722285605628792127127)
  ·
    refine ⟨26539083428408443188190691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17692722285605628792127127 26539083428408443188190691)
    ·
      refine ⟨39808625142612664782286037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26539083428408443188190691 39808625142612664782286037)
      ·
        refine ⟨933014651779984330834829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 39808625142612664782286037 933014651779984330834829)
        ·
          refine ⟨349880494417494124063061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 933014651779984330834829 349880494417494124063061)
          ·
            refine ⟨1025040510988752316591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 349880494417494124063061 1025040510988752316591)
            ·
              rfl

theorem cell23_485091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 10].length) (baseStart_485091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485091 prefixEnd_485091 := by exact prefixLift 485091
  have htrace : WordTrace (prefixWord ++ tailWord_485091) baseStart_485091 baseEnd_485091 := by
    simpa [prefixWord, tailWord_485091, baseEnd_485091] using wordTrace_append hprefix tailTrace_485091
  have hstable : (prefixWord ++ tailWord_485091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485091).length < 2 ^ (prefixWord ++ tailWord_485091).sum := by decide
  have hdescent : baseEnd_485091 < baseStart_485091 := by decide
  rcases family_descends (prefixWord ++ tailWord_485091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485102 : List Nat := [4, 1, 2, 1, 1, 2, 3, 4, 1, 2, 2]
def baseStart_485102 : Nat := 118140960795 + 485102 * 2 ^ 59
def prefixEnd_485102 : Nat := 4983230072969 + 3 ^ 40 * 485102 * 2
def baseEnd_485102 : Nat := 249090492457466269894063

theorem tailTrace_485102 : CollatzResearch.WordTrace tailWord_485102 prefixEnd_485102 249090492457466269894063 := by
  unfold tailWord_485102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2211640436070722208847195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11795415659043851780518373 2211640436070722208847195)
  ·
    refine ⟨3317460654106083313270793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2211640436070722208847195 3317460654106083313270793)
    ·
      refine ⟨2488095490579562484953095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3317460654106083313270793 2488095490579562484953095)
      ·
        refine ⟨3732143235869343727429643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488095490579562484953095 3732143235869343727429643)
        ·
          refine ⟨5598214853804015591144465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732143235869343727429643 5598214853804015591144465)
          ·
            refine ⟨4198661140353011693358349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5598214853804015591144465 4198661140353011693358349)
            ·
              refine ⟨1574497927632379385009381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4198661140353011693358349 1574497927632379385009381)
              ·
                refine ⟨295218361431071134689259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1574497927632379385009381 295218361431071134689259)
                ·
                  refine ⟨442827542146606702033889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295218361431071134689259 442827542146606702033889)
                  ·
                    refine ⟨332120656609955026525417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 442827542146606702033889 332120656609955026525417)
                    ·
                      refine ⟨249090492457466269894063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 332120656609955026525417 249090492457466269894063)
                      ·
                        rfl

theorem cell23_485102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_485102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485102 prefixEnd_485102 := by exact prefixLift 485102
  have htrace : WordTrace (prefixWord ++ tailWord_485102) baseStart_485102 baseEnd_485102 := by
    simpa [prefixWord, tailWord_485102, baseEnd_485102] using wordTrace_append hprefix tailTrace_485102
  have hstable : (prefixWord ++ tailWord_485102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485102).length < 2 ^ (prefixWord ++ tailWord_485102).sum := by decide
  have hdescent : baseEnd_485102 < baseStart_485102 := by decide
  rcases family_descends (prefixWord ++ tailWord_485102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485114 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_485114 : Nat := 118140960795 + 485114 * 2 ^ 59
def prefixEnd_485114 : Nat := 4983230072969 + 3 ^ 40 * 485114 * 2
def baseEnd_485114 : Nat := 249096654225320222944007

theorem tailTrace_485114 : CollatzResearch.WordTrace tailWord_485114 prefixEnd_485114 249096654225320222944007 := by
  unfold tailWord_485114
  simp only [CollatzResearch.WordTrace]
  refine ⟨4423390291130575930053599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11795707443014869146809597 4423390291130575930053599)
  ·
    refine ⟨6635085436695863895080399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4423390291130575930053599 6635085436695863895080399)
    ·
      refine ⟨9952628155043795842620599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6635085436695863895080399 9952628155043795842620599)
      ·
        refine ⟨14928942232565693763930899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9952628155043795842620599 14928942232565693763930899)
        ·
          refine ⟨22393413348848540645896349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14928942232565693763930899 22393413348848540645896349)
          ·
            refine ⟨8397530005818202742211131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22393413348848540645896349 8397530005818202742211131)
            ·
              refine ⟨12596295008727304113316697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8397530005818202742211131 12596295008727304113316697)
              ·
                refine ⟨9447221256545478084987523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12596295008727304113316697 9447221256545478084987523)
                ·
                  refine ⟨14170831884818217127481285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9447221256545478084987523 14170831884818217127481285)
                  ·
                    refine ⟨2657030978403415711402741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14170831884818217127481285 2657030978403415711402741)
                    ·
                      refine ⟨249096654225320222944007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2657030978403415711402741 249096654225320222944007)
                      ·
                        rfl

theorem cell23_485114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_485114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485114 prefixEnd_485114 := by exact prefixLift 485114
  have htrace : WordTrace (prefixWord ++ tailWord_485114) baseStart_485114 baseEnd_485114 := by
    simpa [prefixWord, tailWord_485114, baseEnd_485114] using wordTrace_append hprefix tailTrace_485114
  have hstable : (prefixWord ++ tailWord_485114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485114).length < 2 ^ (prefixWord ++ tailWord_485114).sum := by decide
  have hdescent : baseEnd_485114 < baseStart_485114 := by decide
  rcases family_descends (prefixWord ++ tailWord_485114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485128 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 3, 3, 2]
def baseStart_485128 : Nat := 118140960795 + 485128 * 2 ^ 59
def prefixEnd_485128 : Nat := 4983230072969 + 3 ^ 40 * 485128 * 2
def baseEnd_485128 : Nat := 249103842954483168168943

theorem tailTrace_485128 : CollatzResearch.WordTrace tailWord_485128 prefixEnd_485128 249103842954483168168943 := by
  unfold tailWord_485128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8847035893235792055612019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11796047857647722740816025 8847035893235792055612019)
  ·
    refine ⟨13270553839853688083418029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8847035893235792055612019 13270553839853688083418029)
    ·
      refine ⟨4976457689945133031281761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13270553839853688083418029 4976457689945133031281761)
      ·
        refine ⟨3732343267458849773461321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4976457689945133031281761 3732343267458849773461321)
        ·
          refine ⟨2799257450594137330095991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3732343267458849773461321 2799257450594137330095991)
          ·
            refine ⟨4198886175891205995143987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799257450594137330095991 4198886175891205995143987)
            ·
              refine ⟨6298329263836808992715981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4198886175891205995143987 6298329263836808992715981)
              ·
                refine ⟨2361873473938803372268493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6298329263836808992715981 2361873473938803372268493)
                ·
                  refine ⟨885702552727051264600685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2361873473938803372268493 885702552727051264600685)
                  ·
                    refine ⟨332138457272644224225257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 885702552727051264600685 332138457272644224225257)
                    ·
                      refine ⟨249103842954483168168943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 332138457272644224225257 249103842954483168168943)
                      ·
                        rfl

theorem cell23_485128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_485128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485128 prefixEnd_485128 := by exact prefixLift 485128
  have htrace : WordTrace (prefixWord ++ tailWord_485128) baseStart_485128 baseEnd_485128 := by
    simpa [prefixWord, tailWord_485128, baseEnd_485128] using wordTrace_append hprefix tailTrace_485128
  have hstable : (prefixWord ++ tailWord_485128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485128).length < 2 ^ (prefixWord ++ tailWord_485128).sum := by decide
  have hdescent : baseEnd_485128 < baseStart_485128 := by decide
  rcases family_descends (prefixWord ++ tailWord_485128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485133 : List Nat := [1, 7, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_485133 : Nat := 118140960795 + 485133 * 2 ^ 59
def prefixEnd_485133 : Nat := 4983230072969 + 3 ^ 40 * 485133 * 2
def baseEnd_485133 : Nat := 83035470119251882868807

theorem tailTrace_485133 : CollatzResearch.WordTrace tailWord_485133 prefixEnd_485133 83035470119251882868807 := by
  unfold tailWord_485133
  simp only [CollatzResearch.WordTrace]
  refine ⟨17694254151453469965156053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11796169434302313310104035 17694254151453469965156053)
  ·
    refine ⟨414709081674690702308345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17694254151453469965156053 414709081674690702308345)
    ·
      refine ⟨311031811256018026731259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414709081674690702308345 311031811256018026731259)
      ·
        refine ⟨466547716884027040096889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311031811256018026731259 466547716884027040096889)
        ·
          refine ⟨349910787663020280072667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466547716884027040096889 349910787663020280072667)
          ·
            refine ⟨524866181494530420109001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349910787663020280072667 524866181494530420109001)
            ·
              refine ⟨393649636120897815081751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524866181494530420109001 393649636120897815081751)
              ·
                refine ⟨590474454181346722622627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393649636120897815081751 590474454181346722622627)
                ·
                  refine ⟨885711681272020083933941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590474454181346722622627 885711681272020083933941)
                  ·
                    refine ⟨83035470119251882868807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 885711681272020083933941 83035470119251882868807)
                    ·
                      rfl

theorem cell23_485133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_485133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485133 prefixEnd_485133 := by exact prefixLift 485133
  have htrace : WordTrace (prefixWord ++ tailWord_485133) baseStart_485133 baseEnd_485133 := by
    simpa [prefixWord, tailWord_485133, baseEnd_485133] using wordTrace_append hprefix tailTrace_485133
  have hstable : (prefixWord ++ tailWord_485133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485133).length < 2 ^ (prefixWord ++ tailWord_485133).sum := by decide
  have hdescent : baseEnd_485133 < baseStart_485133 := by decide
  rcases family_descends (prefixWord ++ tailWord_485133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485191 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_485191 : Nat := 118140960795 + 485191 * 2 ^ 59
def prefixEnd_485191 : Nat := 4983230072969 + 3 ^ 40 * 485191 * 2
def baseEnd_485191 : Nat := 249136192235716421681153

theorem tailTrace_485191 : CollatzResearch.WordTrace tailWord_485191 prefixEnd_485191 249136192235716421681153 := by
  unfold tailWord_485191
  simp only [CollatzResearch.WordTrace]
  refine ⟨17696369585243345870767427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11797579723495563913844951 17696369585243345870767427)
  ·
    refine ⟨26544554377865018806151141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17696369585243345870767427 26544554377865018806151141)
    ·
      refine ⟨4977103945849691026153339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26544554377865018806151141 4977103945849691026153339)
      ·
        refine ⟨7465655918774536539230009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4977103945849691026153339 7465655918774536539230009)
        ·
          refine ⟨5599241939080902404422507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7465655918774536539230009 5599241939080902404422507)
          ·
            refine ⟨8398862908621353606633761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5599241939080902404422507 8398862908621353606633761)
            ·
              refine ⟨6299147181466015204975321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8398862908621353606633761 6299147181466015204975321)
              ·
                refine ⟨4724360386099511403731491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6299147181466015204975321 4724360386099511403731491)
                ·
                  refine ⟨7086540579149267105597237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4724360386099511403731491 7086540579149267105597237)
                  ·
                    refine ⟨664363179295243791149741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7086540579149267105597237 664363179295243791149741)
                    ·
                      refine ⟨249136192235716421681153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 664363179295243791149741 249136192235716421681153)
                      ·
                        rfl

theorem cell23_485191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_485191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485191 prefixEnd_485191 := by exact prefixLift 485191
  have htrace : WordTrace (prefixWord ++ tailWord_485191) baseStart_485191 baseEnd_485191 := by
    simpa [prefixWord, tailWord_485191, baseEnd_485191] using wordTrace_append hprefix tailTrace_485191
  have hstable : (prefixWord ++ tailWord_485191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485191).length < 2 ^ (prefixWord ++ tailWord_485191).sum := by decide
  have hdescent : baseEnd_485191 < baseStart_485191 := by decide
  rcases family_descends (prefixWord ++ tailWord_485191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485215 : List Nat := [1, 1, 2, 3, 1, 5, 3, 2, 5]
def baseStart_485215 : Nat := 118140960795 + 485215 * 2 ^ 59
def prefixEnd_485215 : Nat := 4983230072969 + 3 ^ 40 * 485215 * 2
def baseEnd_485215 : Nat := 27683168419047147531227

theorem tailTrace_485215 : CollatzResearch.WordTrace tailWord_485215 prefixEnd_485215 27683168419047147531227 := by
  unfold tailWord_485215
  simp only [CollatzResearch.WordTrace]
  refine ⟨17697244937156397969641099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11798163291437598646427399 17697244937156397969641099)
  ·
    refine ⟨26545867405734596954461649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17697244937156397969641099 26545867405734596954461649)
    ·
      refine ⟨19909400554300947715846237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26545867405734596954461649 19909400554300947715846237)
      ·
        refine ⟨7466025207862855393442339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19909400554300947715846237 7466025207862855393442339)
        ·
          refine ⟨11199037811794283090163509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7466025207862855393442339 11199037811794283090163509)
          ·
            refine ⟨1049909794855714039702829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11199037811794283090163509 1049909794855714039702829)
            ·
              refine ⟨393716173070892764888561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1049909794855714039702829 393716173070892764888561)
              ·
                refine ⟨295287129803169573666421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393716173070892764888561 295287129803169573666421)
                ·
                  refine ⟨27683168419047147531227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 295287129803169573666421 27683168419047147531227)
                  ·
                    rfl

theorem cell23_485215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 5].length) (baseStart_485215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485215 prefixEnd_485215 := by exact prefixLift 485215
  have htrace : WordTrace (prefixWord ++ tailWord_485215) baseStart_485215 baseEnd_485215 := by
    simpa [prefixWord, tailWord_485215, baseEnd_485215] using wordTrace_append hprefix tailTrace_485215
  have hstable : (prefixWord ++ tailWord_485215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485215).length < 2 ^ (prefixWord ++ tailWord_485215).sum := by decide
  have hdescent : baseEnd_485215 < baseStart_485215 := by decide
  rcases family_descends (prefixWord ++ tailWord_485215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485248 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 4]
def baseStart_485248 : Nat := 118140960795 + 485248 * 2 ^ 59
def prefixEnd_485248 : Nat := 4983230072969 + 3 ^ 40 * 485248 * 2
def baseEnd_485248 : Nat := 249165460633022698668391

theorem tailTrace_485248 : CollatzResearch.WordTrace tailWord_485248 prefixEnd_485248 249165460633022698668391 := by
  unfold tailWord_485248
  simp only [CollatzResearch.WordTrace]
  refine ⟨8849224273018422302796199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11798965697357896403728265 8849224273018422302796199)
  ·
    refine ⟨13273836409527633454194299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8849224273018422302796199 13273836409527633454194299)
    ·
      refine ⟨19910754614291450181291449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13273836409527633454194299 19910754614291450181291449)
      ·
        refine ⟨14933065960718587635968587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19910754614291450181291449 14933065960718587635968587)
        ·
          refine ⟨22399598941077881453952881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14933065960718587635968587 22399598941077881453952881)
          ·
            refine ⟨16799699205808411090464661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22399598941077881453952881 16799699205808411090464661)
            ·
              refine ⟨787485900272269269865531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16799699205808411090464661 787485900272269269865531)
              ·
                refine ⟨1181228850408403904798297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787485900272269269865531 1181228850408403904798297)
                ·
                  refine ⟨885921637806302928598723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1181228850408403904798297 885921637806302928598723)
                  ·
                    refine ⟨1328882456709454392898085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 885921637806302928598723 1328882456709454392898085)
                    ·
                      refine ⟨249165460633022698668391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1328882456709454392898085 249165460633022698668391)
                      ·
                        rfl

theorem cell23_485248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_485248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485248 prefixEnd_485248 := by exact prefixLift 485248
  have htrace : WordTrace (prefixWord ++ tailWord_485248) baseStart_485248 baseEnd_485248 := by
    simpa [prefixWord, tailWord_485248, baseEnd_485248] using wordTrace_append hprefix tailTrace_485248
  have hstable : (prefixWord ++ tailWord_485248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485248).length < 2 ^ (prefixWord ++ tailWord_485248).sum := by decide
  have hdescent : baseEnd_485248 < baseStart_485248 := by decide
  rcases family_descends (prefixWord ++ tailWord_485248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485282 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_485282 : Nat := 118140960795 + 485282 * 2 ^ 59
def prefixEnd_485282 : Nat := 4983230072969 + 3 ^ 40 * 485282 * 2
def baseEnd_485282 : Nat := 249182918975275565643235

theorem tailTrace_485282 : CollatzResearch.WordTrace tailWord_485282 prefixEnd_485282 249182918975275565643235 := by
  unfold tailWord_485282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424922156978417103082525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11799792418609112274886733 4424922156978417103082525)
  ·
    refine ⟨1659345808866906413655947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4424922156978417103082525 1659345808866906413655947)
    ·
      refine ⟨2489018713300359620483921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659345808866906413655947 2489018713300359620483921)
      ·
        refine ⟨1866764034975269715362941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2489018713300359620483921 1866764034975269715362941)
        ·
          refine ⟨700036513115726143261103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1866764034975269715362941 700036513115726143261103)
          ·
            refine ⟨1050054769673589214891655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700036513115726143261103 1050054769673589214891655)
            ·
              refine ⟨1575082154510383822337483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050054769673589214891655 1575082154510383822337483)
              ·
                refine ⟨2362623231765575733506225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575082154510383822337483 2362623231765575733506225)
                ·
                  refine ⟨1771967423824181800129669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2362623231765575733506225 1771967423824181800129669)
                  ·
                    refine ⟨332243891967034087524313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1771967423824181800129669 332243891967034087524313)
                    ·
                      refine ⟨249182918975275565643235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 332243891967034087524313 249182918975275565643235)
                      ·
                        rfl

theorem cell23_485282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_485282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485282 prefixEnd_485282 := by exact prefixLift 485282
  have htrace : WordTrace (prefixWord ++ tailWord_485282) baseStart_485282 baseEnd_485282 := by
    simpa [prefixWord, tailWord_485282, baseEnd_485282] using wordTrace_append hprefix tailTrace_485282
  have hstable : (prefixWord ++ tailWord_485282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485282).length < 2 ^ (prefixWord ++ tailWord_485282).sum := by decide
  have hdescent : baseEnd_485282 < baseStart_485282 := by decide
  rcases family_descends (prefixWord ++ tailWord_485282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485332 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_485332 : Nat := 118140960795 + 485332 * 2 ^ 59
def prefixEnd_485332 : Nat := 4983230072969 + 3 ^ 40 * 485332 * 2
def baseEnd_485332 : Nat := 249208593008000370018005

theorem tailTrace_485332 : CollatzResearch.WordTrace tailWord_485332 prefixEnd_485332 249208593008000370018005 := by
  unfold tailWord_485332
  simp only [CollatzResearch.WordTrace]
  refine ⟨8850756138866263475825125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11801008185155017967766833 8850756138866263475825125)
  ·
    refine ⟨1659516776037424401717211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8850756138866263475825125 1659516776037424401717211)
    ·
      refine ⟨2489275164056136602575817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659516776037424401717211 2489275164056136602575817)
      ·
        refine ⟨1866956373042102451931863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2489275164056136602575817 1866956373042102451931863)
        ·
          refine ⟨2800434559563153677897795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866956373042102451931863 2800434559563153677897795)
          ·
            refine ⟨4200651839344730516846693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2800434559563153677897795 4200651839344730516846693)
            ·
              refine ⟨787622219877136971908755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4200651839344730516846693 787622219877136971908755)
              ·
                refine ⟨1181433329815705457863133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787622219877136971908755 1181433329815705457863133)
                ·
                  refine ⟨443037498680889546698675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181433329815705457863133 443037498680889546698675)
                  ·
                    refine ⟨664556248021334320048013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 443037498680889546698675 664556248021334320048013)
                    ·
                      refine ⟨249208593008000370018005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 664556248021334320048013 249208593008000370018005)
                      ·
                        rfl

theorem cell23_485332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_485332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485332 prefixEnd_485332 := by exact prefixLift 485332
  have htrace : WordTrace (prefixWord ++ tailWord_485332) baseStart_485332 baseEnd_485332 := by
    simpa [prefixWord, tailWord_485332, baseEnd_485332] using wordTrace_append hprefix tailTrace_485332
  have hstable : (prefixWord ++ tailWord_485332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485332).length < 2 ^ (prefixWord ++ tailWord_485332).sum := by decide
  have hdescent : baseEnd_485332 < baseStart_485332 := by decide
  rcases family_descends (prefixWord ++ tailWord_485332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485368 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 1, 2, 4]
def baseStart_485368 : Nat := 118140960795 + 485368 * 2 ^ 59
def prefixEnd_485368 : Nat := 4983230072969 + 3 ^ 40 * 485368 * 2
def baseEnd_485368 : Nat := 249227078311562229167839

theorem tailTrace_485368 : CollatzResearch.WordTrace tailWord_485368 prefixEnd_485368 249227078311562229167839 := by
  unfold tailWord_485368
  simp only [CollatzResearch.WordTrace]
  refine ⟨8851412652801052549980379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11801883537068070066640505 8851412652801052549980379)
  ·
    refine ⟨13277118979201578824970569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8851412652801052549980379 13277118979201578824970569)
    ·
      refine ⟨9957839234401184118727927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13277118979201578824970569 9957839234401184118727927)
      ·
        refine ⟨14936758851601776178091891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9957839234401184118727927 14936758851601776178091891)
        ·
          refine ⟨22405138277402664267137837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14936758851601776178091891 22405138277402664267137837)
          ·
            refine ⟨8401926854025999100176689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22405138277402664267137837 8401926854025999100176689)
            ·
              refine ⟨6301445140519499325132517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8401926854025999100176689 6301445140519499325132517)
              ·
                refine ⟨1181520963847406123462347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6301445140519499325132517 1181520963847406123462347)
                ·
                  refine ⟨1772281445771109185193521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181520963847406123462347 1772281445771109185193521)
                  ·
                    refine ⟨1329211084328331888895141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1772281445771109185193521 1329211084328331888895141)
                    ·
                      refine ⟨249227078311562229167839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1329211084328331888895141 249227078311562229167839)
                      ·
                        rfl

theorem cell23_485368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_485368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485368 prefixEnd_485368 := by exact prefixLift 485368
  have htrace : WordTrace (prefixWord ++ tailWord_485368) baseStart_485368 baseEnd_485368 := by
    simpa [prefixWord, tailWord_485368, baseEnd_485368] using wordTrace_append hprefix tailTrace_485368
  have hstable : (prefixWord ++ tailWord_485368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485368).length < 2 ^ (prefixWord ++ tailWord_485368).sum := by decide
  have hdescent : baseEnd_485368 < baseStart_485368 := by decide
  rcases family_descends (prefixWord ++ tailWord_485368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485409 : List Nat := [1, 2, 3, 2, 4, 2, 1, 2, 1, 2, 3]
def baseStart_485409 : Nat := 118140960795 + 485409 * 2 ^ 59
def prefixEnd_485409 : Nat := 4983230072969 + 3 ^ 40 * 485409 * 2
def baseEnd_485409 : Nat := 249248131018396568755151

theorem tailTrace_485409 : CollatzResearch.WordTrace tailWord_485409 prefixEnd_485409 249248131018396568755151 := by
  unfold tailWord_485409
  simp only [CollatzResearch.WordTrace]
  refine ⟨17704320698453569102203281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11802880465635712734802187 17704320698453569102203281)
  ·
    refine ⟨13278240523840176826652461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17704320698453569102203281 13278240523840176826652461)
    ·
      refine ⟨4979340196440066309994673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13278240523840176826652461 4979340196440066309994673)
      ·
        refine ⟨3734505147330049732496005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4979340196440066309994673 3734505147330049732496005)
        ·
          refine ⟨700219715124384324843001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3734505147330049732496005 700219715124384324843001)
          ·
            refine ⟨525164786343288243632251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700219715124384324843001 525164786343288243632251)
            ·
              refine ⟨787747179514932365448377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525164786343288243632251 787747179514932365448377)
              ·
                refine ⟨590810384636199274086283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787747179514932365448377 590810384636199274086283)
                ·
                  refine ⟨886215576954298911129425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590810384636199274086283 886215576954298911129425)
                  ·
                    refine ⟨664661682715724183347069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 886215576954298911129425 664661682715724183347069)
                    ·
                      refine ⟨249248131018396568755151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 664661682715724183347069 249248131018396568755151)
                      ·
                        rfl

theorem cell23_485409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_485409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485409 prefixEnd_485409 := by exact prefixLift 485409
  have htrace : WordTrace (prefixWord ++ tailWord_485409) baseStart_485409 baseEnd_485409 := by
    simpa [prefixWord, tailWord_485409, baseEnd_485409] using wordTrace_append hprefix tailTrace_485409
  have hstable : (prefixWord ++ tailWord_485409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485409).length < 2 ^ (prefixWord ++ tailWord_485409).sum := by decide
  have hdescent : baseEnd_485409 < baseStart_485409 := by decide
  rcases family_descends (prefixWord ++ tailWord_485409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485422 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_485422 : Nat := 118140960795 + 485422 * 2 ^ 59
def prefixEnd_485422 : Nat := 4983230072969 + 3 ^ 40 * 485422 * 2
def baseEnd_485422 : Nat := 249254806266905017892591

theorem tailTrace_485422 : CollatzResearch.WordTrace tailWord_485422 prefixEnd_485422 249254806266905017892591 := by
  unfold tailWord_485422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2213099355925809040303315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11803196564937648214951013 2213099355925809040303315)
  ·
    refine ⟨3319649033888713560454973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2213099355925809040303315 3319649033888713560454973)
    ·
      refine ⟨1244868387708267585170615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3319649033888713560454973 1244868387708267585170615)
      ·
        refine ⟨1867302581562401377755923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244868387708267585170615 1867302581562401377755923)
        ·
          refine ⟨2800953872343602066633885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867302581562401377755923 2800953872343602066633885)
          ·
            refine ⟨1050357702128850774987707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2800953872343602066633885 1050357702128850774987707)
            ·
              refine ⟨1575536553193276162481561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050357702128850774987707 1575536553193276162481561)
              ·
                refine ⟨1181652414894957121861171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1575536553193276162481561 1181652414894957121861171)
                ·
                  refine ⟨1772478622342435682791757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181652414894957121861171 1772478622342435682791757)
                  ·
                    refine ⟨664679483378413381046909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772478622342435682791757 664679483378413381046909)
                    ·
                      refine ⟨249254806266905017892591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 664679483378413381046909 249254806266905017892591)
                      ·
                        rfl

theorem cell23_485422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_485422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485422 prefixEnd_485422 := by exact prefixLift 485422
  have htrace : WordTrace (prefixWord ++ tailWord_485422) baseStart_485422 baseEnd_485422 := by
    simpa [prefixWord, tailWord_485422, baseEnd_485422] using wordTrace_append hprefix tailTrace_485422
  have hstable : (prefixWord ++ tailWord_485422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485422).length < 2 ^ (prefixWord ++ tailWord_485422).sum := by decide
  have hdescent : baseEnd_485422 < baseStart_485422 := by decide
  rcases family_descends (prefixWord ++ tailWord_485422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485445 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 5, 4, 2]
def baseStart_485445 : Nat := 118140960795 + 485445 * 2 ^ 59
def prefixEnd_485445 : Nat := 4983230072969 + 3 ^ 40 * 485445 * 2
def baseEnd_485445 : Nat := 249266616321958427904985

theorem tailTrace_485445 : CollatzResearch.WordTrace tailWord_485445 prefixEnd_485445 249266616321958427904985 := by
  unfold tailWord_485445
  simp only [CollatzResearch.WordTrace]
  refine ⟨17705633726323147250513789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11803755817548764833675859 17705633726323147250513789)
  ·
    refine ⟨6639612647371180218942671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17705633726323147250513789 6639612647371180218942671)
    ·
      refine ⟨9959418971056770328414007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6639612647371180218942671 9959418971056770328414007)
      ·
        refine ⟨14939128456585155492621011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9959418971056770328414007 14939128456585155492621011)
        ·
          refine ⟨22408692684877733238931517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14939128456585155492621011 22408692684877733238931517)
          ·
            refine ⟨8403259756829149964599319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22408692684877733238931517 8403259756829149964599319)
            ·
              refine ⟨12604889635243724946898979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8403259756829149964599319 12604889635243724946898979)
              ·
                refine ⟨18907334452865587420348469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12604889635243724946898979 18907334452865587420348469)
                ·
                  refine ⟨1772562604956148820657669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18907334452865587420348469 1772562604956148820657669)
                  ·
                    refine ⟨332355488429277903873313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1772562604956148820657669 332355488429277903873313)
                    ·
                      refine ⟨249266616321958427904985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 332355488429277903873313 249266616321958427904985)
                      ·
                        rfl

theorem cell23_485445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 4, 2].length) (baseStart_485445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485445 prefixEnd_485445 := by exact prefixLift 485445
  have htrace : WordTrace (prefixWord ++ tailWord_485445) baseStart_485445 baseEnd_485445 := by
    simpa [prefixWord, tailWord_485445, baseEnd_485445] using wordTrace_append hprefix tailTrace_485445
  have hstable : (prefixWord ++ tailWord_485445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485445).length < 2 ^ (prefixWord ++ tailWord_485445).sum := by decide
  have hdescent : baseEnd_485445 < baseStart_485445 := by decide
  rcases family_descends (prefixWord ++ tailWord_485445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485448 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_485448 : Nat := 118140960795 + 485448 * 2 ^ 59
def prefixEnd_485448 : Nat := 4983230072969 + 3 ^ 40 * 485448 * 2
def baseEnd_485448 : Nat := 249268156763921916167471

theorem tailTrace_485448 : CollatzResearch.WordTrace tailWord_485448 prefixEnd_485448 249268156763921916167471 := by
  unfold tailWord_485448
  simp only [CollatzResearch.WordTrace]
  refine ⟨8852871572656139381436499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11803828763541519175248665 8852871572656139381436499)
  ·
    refine ⟨13279307358984209072154749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8852871572656139381436499 13279307358984209072154749)
    ·
      refine ⟨4979740259619078402058031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13279307358984209072154749 4979740259619078402058031)
      ·
        refine ⟨7469610389428617603087047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4979740259619078402058031 7469610389428617603087047)
        ·
          refine ⟨11204415584142926404630571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7469610389428617603087047 11204415584142926404630571)
          ·
            refine ⟨16806623376214389606945857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11204415584142926404630571 16806623376214389606945857)
            ·
              refine ⟨12604967532160792205209393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16806623376214389606945857 12604967532160792205209393)
              ·
                refine ⟨9453725649120594153907045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12604967532160792205209393 9453725649120594153907045)
                ·
                  refine ⟨1772573559210111403857571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9453725649120594153907045 1772573559210111403857571)
                  ·
                    refine ⟨2658860338815167105786357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1772573559210111403857571 2658860338815167105786357)
                    ·
                      refine ⟨249268156763921916167471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2658860338815167105786357 249268156763921916167471)
                      ·
                        rfl

theorem cell23_485448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_485448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485448 prefixEnd_485448 := by exact prefixLift 485448
  have htrace : WordTrace (prefixWord ++ tailWord_485448) baseStart_485448 baseEnd_485448 := by
    simpa [prefixWord, tailWord_485448, baseEnd_485448] using wordTrace_append hprefix tailTrace_485448
  have hstable : (prefixWord ++ tailWord_485448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485448).length < 2 ^ (prefixWord ++ tailWord_485448).sum := by decide
  have hdescent : baseEnd_485448 < baseStart_485448 := by decide
  rcases family_descends (prefixWord ++ tailWord_485448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485495 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 3]
def baseStart_485495 : Nat := 118140960795 + 485495 * 2 ^ 59
def prefixEnd_485495 : Nat := 4983230072969 + 3 ^ 40 * 485495 * 2
def baseEnd_485495 : Nat := 249292290354683232279755

theorem tailTrace_485495 : CollatzResearch.WordTrace tailWord_485495 prefixEnd_485495 249292290354683232279755 := by
  unfold tailWord_485495
  simp only [CollatzResearch.WordTrace]
  refine ⟨17707457376142005789833939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11804971584094670526555959 17707457376142005789833939)
  ·
    refine ⟨26561186064213008684750909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17707457376142005789833939 26561186064213008684750909)
    ·
      refine ⟨9960444774079878256781591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26561186064213008684750909 9960444774079878256781591)
      ·
        refine ⟨14940667161119817385172387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9960444774079878256781591 14940667161119817385172387)
        ·
          refine ⟨22411000741679726077758581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14940667161119817385172387 22411000741679726077758581)
          ·
            refine ⟨2101031319532474319789867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22411000741679726077758581 2101031319532474319789867)
            ·
              refine ⟨3151546979298711479684801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101031319532474319789867 3151546979298711479684801)
              ·
                refine ⟨2363660234474033609763601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3151546979298711479684801 2363660234474033609763601)
                ·
                  refine ⟨1772745175855525207322701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2363660234474033609763601 1772745175855525207322701)
                  ·
                    refine ⟨664779440945821952746013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772745175855525207322701 664779440945821952746013)
                    ·
                      refine ⟨249292290354683232279755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 664779440945821952746013 249292290354683232279755)
                      ·
                        rfl

theorem cell23_485495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_485495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485495 prefixEnd_485495 := by exact prefixLift 485495
  have htrace : WordTrace (prefixWord ++ tailWord_485495) baseStart_485495 baseEnd_485495 := by
    simpa [prefixWord, tailWord_485495, baseEnd_485495] using wordTrace_append hprefix tailTrace_485495
  have hstable : (prefixWord ++ tailWord_485495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485495).length < 2 ^ (prefixWord ++ tailWord_485495).sum := by decide
  have hdescent : baseEnd_485495 < baseStart_485495 := by decide
  rcases family_descends (prefixWord ++ tailWord_485495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485512 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_485512 : Nat := 118140960795 + 485512 * 2 ^ 59
def prefixEnd_485512 : Nat := 4983230072969 + 3 ^ 40 * 485512 * 2
def baseEnd_485512 : Nat := 249301019525809665767177

theorem tailTrace_485512 : CollatzResearch.WordTrace tailWord_485512 prefixEnd_485512 249301019525809665767177 := by
  unfold tailWord_485512
  simp only [CollatzResearch.WordTrace]
  refine ⟨8854038708540208846601395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11805384944720278462135193 8854038708540208846601395)
  ·
    refine ⟨13281058062810313269902093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8854038708540208846601395 13281058062810313269902093)
    ·
      refine ⟨4980396773553867476213285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13281058062810313269902093 4980396773553867476213285)
      ·
        refine ⟨933824395041350151789991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4980396773553867476213285 933824395041350151789991)
        ·
          refine ⟨1400736592562025227684987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933824395041350151789991 1400736592562025227684987)
          ·
            refine ⟨2101104888843037841527481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400736592562025227684987 2101104888843037841527481)
            ·
              refine ⟨1575828666632278381145611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2101104888843037841527481 1575828666632278381145611)
              ·
                refine ⟨2363742999948417571718417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575828666632278381145611 2363742999948417571718417)
                ·
                  refine ⟨1772807249961313178788813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2363742999948417571718417 1772807249961313178788813)
                  ·
                    refine ⟨664802718735492442045805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772807249961313178788813 664802718735492442045805)
                    ·
                      refine ⟨249301019525809665767177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 664802718735492442045805 249301019525809665767177)
                      ·
                        rfl

theorem cell23_485512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_485512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485512 prefixEnd_485512 := by exact prefixLift 485512
  have htrace : WordTrace (prefixWord ++ tailWord_485512) baseStart_485512 baseEnd_485512 := by
    simpa [prefixWord, tailWord_485512, baseEnd_485512] using wordTrace_append hprefix tailTrace_485512
  have hstable : (prefixWord ++ tailWord_485512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485512).length < 2 ^ (prefixWord ++ tailWord_485512).sum := by decide
  have hdescent : baseEnd_485512 < baseStart_485512 := by decide
  rcases family_descends (prefixWord ++ tailWord_485512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485562 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 3, 4]
def baseStart_485562 : Nat := 118140960795 + 485562 * 2 ^ 59
def prefixEnd_485562 : Nat := 4983230072969 + 3 ^ 40 * 485562 * 2
def baseEnd_485562 : Nat := 83108897852844823380649

theorem tailTrace_485562 : CollatzResearch.WordTrace tailWord_485562 prefixEnd_485562 83108897852844823380649 := by
  unfold tailWord_485562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4427475266724819058130735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11806600711266184155015293 4427475266724819058130735)
  ·
    refine ⟨6641212900087228587196103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4427475266724819058130735 6641212900087228587196103)
    ·
      refine ⟨9961819350130842880794155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6641212900087228587196103 9961819350130842880794155)
      ·
        refine ⟨14942729025196264321191233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9961819350130842880794155 14942729025196264321191233)
        ·
          refine ⟨11207046768897198240893425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14942729025196264321191233 11207046768897198240893425)
          ·
            refine ⟨8405285076672898680670069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11207046768897198240893425 8405285076672898680670069)
            ·
              refine ⟨787995475938084251312819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8405285076672898680670069 787995475938084251312819)
              ·
                refine ⟨1181993213907126376969229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787995475938084251312819 1181993213907126376969229)
                ·
                  refine ⟨443247455215172391363461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181993213907126376969229 443247455215172391363461)
                  ·
                    refine ⟨83108897852844823380649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 443247455215172391363461 83108897852844823380649)
                    ·
                      rfl

theorem cell23_485562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_485562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485562 prefixEnd_485562 := by exact prefixLift 485562
  have htrace : WordTrace (prefixWord ++ tailWord_485562) baseStart_485562 baseEnd_485562 := by
    simpa [prefixWord, tailWord_485562, baseEnd_485562] using wordTrace_append hprefix tailTrace_485562
  have hstable : (prefixWord ++ tailWord_485562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485562).length < 2 ^ (prefixWord ++ tailWord_485562).sum := by decide
  have hdescent : baseEnd_485562 < baseStart_485562 := by decide
  rcases family_descends (prefixWord ++ tailWord_485562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485585 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 2, 5, 3]
def baseStart_485585 : Nat := 118140960795 + 485585 * 2 ^ 59
def prefixEnd_485585 : Nat := 4983230072969 + 3 ^ 40 * 485585 * 2
def baseEnd_485585 : Nat := 249338503613587880154341

theorem tailTrace_485585 : CollatzResearch.WordTrace tailWord_485585 prefixEnd_485585 249338503613587880154341 := by
  unfold tailWord_485585
  simp only [CollatzResearch.WordTrace]
  refine ⟨17710739945815951160610209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11807159963877300773740139 17710739945815951160610209)
  ·
    refine ⟨13283054959361963370457657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17710739945815951160610209 13283054959361963370457657)
    ·
      refine ⟨9962291219521472527843243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13283054959361963370457657 9962291219521472527843243)
      ·
        refine ⟨14943436829282208791764865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9962291219521472527843243 14943436829282208791764865)
        ·
          refine ⟨11207577621961656593823649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14943436829282208791764865 11207577621961656593823649)
          ·
            refine ⟨8405683216471242445367737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11207577621961656593823649 8405683216471242445367737)
            ·
              refine ⟨6304262412353431834025803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8405683216471242445367737 6304262412353431834025803)
              ·
                refine ⟨9456393618530147751038705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304262412353431834025803 9456393618530147751038705)
                ·
                  refine ⟨7092295213897610813279029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9456393618530147751038705 7092295213897610813279029)
                  ·
                    refine ⟨664902676302901013744909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7092295213897610813279029 664902676302901013744909)
                    ·
                      refine ⟨249338503613587880154341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 664902676302901013744909 249338503613587880154341)
                      ·
                        rfl

theorem cell23_485585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_485585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485585 prefixEnd_485585 := by exact prefixLift 485585
  have htrace : WordTrace (prefixWord ++ tailWord_485585) baseStart_485585 baseEnd_485585 := by
    simpa [prefixWord, tailWord_485585, baseEnd_485585] using wordTrace_append hprefix tailTrace_485585
  have hstable : (prefixWord ++ tailWord_485585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485585).length < 2 ^ (prefixWord ++ tailWord_485585).sum := by decide
  have hdescent : baseEnd_485585 < baseStart_485585 := by decide
  rcases family_descends (prefixWord ++ tailWord_485585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485622 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_485622 : Nat := 118140960795 + 485622 * 2 ^ 59
def prefixEnd_485622 : Nat := 4983230072969 + 3 ^ 40 * 485622 * 2
def baseEnd_485622 : Nat := 83119167465934745130557

theorem tailTrace_485622 : CollatzResearch.WordTrace tailWord_485622 prefixEnd_485622 83119167465934745130557 := by
  unfold tailWord_485622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1107005590417619154981695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11808059631121270986471413 1107005590417619154981695)
  ·
    refine ⟨1660508385626428732472543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1107005590417619154981695 1660508385626428732472543)
    ·
      refine ⟨2490762578439643098708815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1660508385626428732472543 2490762578439643098708815)
      ·
        refine ⟨3736143867659464648063223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490762578439643098708815 3736143867659464648063223)
        ·
          refine ⟨5604215801489196972094835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3736143867659464648063223 5604215801489196972094835)
          ·
            refine ⟨8406323702233795458142253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5604215801489196972094835 8406323702233795458142253)
            ·
              refine ⟨3152371388337673296803345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8406323702233795458142253 3152371388337673296803345)
              ·
                refine ⟨2364278541253254972602509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3152371388337673296803345 2364278541253254972602509)
                ·
                  refine ⟨886604452969970614725941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2364278541253254972602509 886604452969970614725941)
                  ·
                    refine ⟨83119167465934745130557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 886604452969970614725941 83119167465934745130557)
                    ·
                      rfl

theorem cell23_485622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_485622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485622 prefixEnd_485622 := by exact prefixLift 485622
  have htrace : WordTrace (prefixWord ++ tailWord_485622) baseStart_485622 baseEnd_485622 := by
    simpa [prefixWord, tailWord_485622, baseEnd_485622] using wordTrace_append hprefix tailTrace_485622
  have hstable : (prefixWord ++ tailWord_485622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485622).length < 2 ^ (prefixWord ++ tailWord_485622).sum := by decide
  have hdescent : baseEnd_485622 < baseStart_485622 := by decide
  rcases family_descends (prefixWord ++ tailWord_485622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485636 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_485636 : Nat := 118140960795 + 485636 * 2 ^ 59
def prefixEnd_485636 : Nat := 4983230072969 + 3 ^ 40 * 485636 * 2
def baseEnd_485636 : Nat := 249364691126967180616607

theorem tailTrace_485636 : CollatzResearch.WordTrace tailWord_485636 prefixEnd_485636 249364691126967180616607 := by
  unfold tailWord_485636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8856300034315593435358381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11808400045754124580477841 8856300034315593435358381)
  ·
    refine ⟨3321112512868347538259393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8856300034315593435358381 3321112512868347538259393)
    ·
      refine ⟨2490834384651260653694545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3321112512868347538259393 2490834384651260653694545)
      ·
        refine ⟨1868125788488445490270909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2490834384651260653694545 1868125788488445490270909)
        ·
          refine ⟨700547170683167058851591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1868125788488445490270909 700547170683167058851591)
          ·
            refine ⟨1050820756024750588277387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700547170683167058851591 1050820756024750588277387)
            ·
              refine ⟨1576231134037125882416081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050820756024750588277387 1576231134037125882416081)
              ·
                refine ⟨1182173350527844411812061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576231134037125882416081 1182173350527844411812061)
                ·
                  refine ⟨443315006447941654429523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182173350527844411812061 443315006447941654429523)
                  ·
                    refine ⟨664972509671912481644285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 443315006447941654429523 664972509671912481644285)
                    ·
                      refine ⟨249364691126967180616607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 664972509671912481644285 249364691126967180616607)
                      ·
                        rfl

theorem cell23_485636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_485636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485636 prefixEnd_485636 := by exact prefixLift 485636
  have htrace : WordTrace (prefixWord ++ tailWord_485636) baseStart_485636 baseEnd_485636 := by
    simpa [prefixWord, tailWord_485636, baseEnd_485636] using wordTrace_append hprefix tailTrace_485636
  have hstable : (prefixWord ++ tailWord_485636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485636).length < 2 ^ (prefixWord ++ tailWord_485636).sum := by decide
  have hdescent : baseEnd_485636 < baseStart_485636 := by decide
  rcases family_descends (prefixWord ++ tailWord_485636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485642 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_485642 : Nat := 118140960795 + 485642 * 2 ^ 59
def prefixEnd_485642 : Nat := 4983230072969 + 3 ^ 40 * 485642 * 2
def baseEnd_485642 : Nat := 249367772010894157141579

theorem tailTrace_485642 : CollatzResearch.WordTrace tailWord_485642 prefixEnd_485642 249367772010894157141579 := by
  unfold tailWord_485642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4428204726652362473858795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11808545937739633263623453 4428204726652362473858795)
  ·
    refine ⟨6642307089978543710788193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4428204726652362473858795 6642307089978543710788193)
    ·
      refine ⟨4981730317483907783091145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6642307089978543710788193 4981730317483907783091145)
      ·
        refine ⟨3736297738112930837318359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4981730317483907783091145 3736297738112930837318359)
        ·
          refine ⟨5604446607169396255977539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3736297738112930837318359 5604446607169396255977539)
          ·
            refine ⟨8406669910754094383966309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5604446607169396255977539 8406669910754094383966309)
            ·
              refine ⟨1576250608266392696993683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8406669910754094383966309 1576250608266392696993683)
              ·
                refine ⟨2364375912399589045490525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1576250608266392696993683 2364375912399589045490525)
                ·
                  refine ⟨886640967149845892058947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2364375912399589045490525 886640967149845892058947)
                  ·
                    refine ⟨1329961450724768838088421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 886640967149845892058947 1329961450724768838088421)
                    ·
                      refine ⟨249367772010894157141579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1329961450724768838088421 249367772010894157141579)
                      ·
                        rfl

theorem cell23_485642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_485642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485642 prefixEnd_485642 := by exact prefixLift 485642
  have htrace : WordTrace (prefixWord ++ tailWord_485642) baseStart_485642 baseEnd_485642 := by
    simpa [prefixWord, tailWord_485642, baseEnd_485642] using wordTrace_append hprefix tailTrace_485642
  have hstable : (prefixWord ++ tailWord_485642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485642).length < 2 ^ (prefixWord ++ tailWord_485642).sum := by decide
  have hdescent : baseEnd_485642 < baseStart_485642 := by decide
  rcases family_descends (prefixWord ++ tailWord_485642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485659 : List Nat := [1, 1, 1, 1, 1, 1, 10, 1, 1, 1, 4]
def baseStart_485659 : Nat := 118140960795 + 485659 * 2 ^ 59
def prefixEnd_485659 : Nat := 4983230072969 + 3 ^ 40 * 485659 * 2
def baseEnd_485659 : Nat := 249376501182020590629001

theorem tailTrace_485659 : CollatzResearch.WordTrace tailWord_485659 prefixEnd_485659 249376501182020590629001 := by
  unfold tailWord_485659
  simp only [CollatzResearch.WordTrace]
  refine ⟨17713438947547861798804031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11808959298365241199202687 17713438947547861798804031)
  ·
    refine ⟨26570158421321792698206047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17713438947547861798804031 26570158421321792698206047)
    ·
      refine ⟨39855237631982689047309071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26570158421321792698206047 39855237631982689047309071)
      ·
        refine ⟨59782856447974033570963607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39855237631982689047309071 59782856447974033570963607)
        ·
          refine ⟨89674284671961050356445411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59782856447974033570963607 89674284671961050356445411)
          ·
            refine ⟨134511427007941575534668117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89674284671961050356445411 134511427007941575534668117)
            ·
              refine ⟨394076446312328834574223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 134511427007941575534668117 394076446312328834574223)
              ·
                refine ⟨591114669468493251861335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394076446312328834574223 591114669468493251861335)
                ·
                  refine ⟨886672004202739877792003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591114669468493251861335 886672004202739877792003)
                  ·
                    refine ⟨1330008006304109816688005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 886672004202739877792003 1330008006304109816688005)
                    ·
                      refine ⟨249376501182020590629001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1330008006304109816688005 249376501182020590629001)
                      ·
                        rfl

theorem cell23_485659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 1, 1, 4].length) (baseStart_485659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485659 prefixEnd_485659 := by exact prefixLift 485659
  have htrace : WordTrace (prefixWord ++ tailWord_485659) baseStart_485659 baseEnd_485659 := by
    simpa [prefixWord, tailWord_485659, baseEnd_485659] using wordTrace_append hprefix tailTrace_485659
  have hstable : (prefixWord ++ tailWord_485659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485659).length < 2 ^ (prefixWord ++ tailWord_485659).sum := by decide
  have hdescent : baseEnd_485659 < baseStart_485659 := by decide
  rcases family_descends (prefixWord ++ tailWord_485659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485669 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 4, 4]
def baseStart_485669 : Nat := 118140960795 + 485669 * 2 ^ 59
def prefixEnd_485669 : Nat := 4983230072969 + 3 ^ 40 * 485669 * 2
def baseEnd_485669 : Nat := 83127211996188517167985

theorem tailTrace_485669 : CollatzResearch.WordTrace tailWord_485669 prefixEnd_485669 83127211996188517167985 := by
  unfold tailWord_485669
  simp only [CollatzResearch.WordTrace]
  refine ⟨17713803677511633506668061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11809202451674422337778707 17713803677511633506668061)
  ·
    refine ⟨6642676379066862565000523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17713803677511633506668061 6642676379066862565000523)
    ·
      refine ⟨9964014568600293847500785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6642676379066862565000523 9964014568600293847500785)
      ·
        refine ⟨7473010926450220385625589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9964014568600293847500785 7473010926450220385625589)
        ·
          refine ⟨700594774354708161152399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7473010926450220385625589 700594774354708161152399)
          ·
            refine ⟨1050892161532062241728599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700594774354708161152399 1050892161532062241728599)
            ·
              refine ⟨1576338242298093362592899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050892161532062241728599 1576338242298093362592899)
              ·
                refine ⟨2364507363447140043889349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1576338242298093362592899 2364507363447140043889349)
                ·
                  refine ⟨443345130646338758229253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2364507363447140043889349 443345130646338758229253)
                  ·
                    refine ⟨83127211996188517167985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 443345130646338758229253 83127211996188517167985)
                    ·
                      rfl

theorem cell23_485669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_485669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485669 prefixEnd_485669 := by exact prefixLift 485669
  have htrace : WordTrace (prefixWord ++ tailWord_485669) baseStart_485669 baseEnd_485669 := by
    simpa [prefixWord, tailWord_485669, baseEnd_485669] using wordTrace_append hprefix tailTrace_485669
  have hstable : (prefixWord ++ tailWord_485669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485669).length < 2 ^ (prefixWord ++ tailWord_485669).sum := by decide
  have hdescent : baseEnd_485669 < baseStart_485669 := by decide
  rcases family_descends (prefixWord ++ tailWord_485669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485689 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 1, 2, 4]
def baseStart_485689 : Nat := 118140960795 + 485689 * 2 ^ 59
def prefixEnd_485689 : Nat := 4983230072969 + 3 ^ 40 * 485689 * 2
def baseEnd_485689 : Nat := 249391905601655473253863

theorem tailTrace_485689 : CollatzResearch.WordTrace tailWord_485689 prefixEnd_485689 249391905601655473253863 := by
  unfold tailWord_485689
  simp only [CollatzResearch.WordTrace]
  refine ⟨17714533137439176922396121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11809688758292784614930747 17714533137439176922396121)
  ·
    refine ⟨13285899853079382691797091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17714533137439176922396121 13285899853079382691797091)
    ·
      refine ⟨19928849779619074037695637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13285899853079382691797091 19928849779619074037695637)
      ·
        refine ⟨934164833419644095516983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19928849779619074037695637 934164833419644095516983)
        ·
          refine ⟨1401247250129466143275475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934164833419644095516983 1401247250129466143275475)
          ·
            refine ⟨2101870875194199214913213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401247250129466143275475 2101870875194199214913213)
            ·
              refine ⟨788201578197824705592455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2101870875194199214913213 788201578197824705592455)
              ·
                refine ⟨1182302367296737058388683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788201578197824705592455 1182302367296737058388683)
                ·
                  refine ⟨1773453550945105587583025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182302367296737058388683 1773453550945105587583025)
                  ·
                    refine ⟨1330090163208829190687269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1773453550945105587583025 1330090163208829190687269)
                    ·
                      refine ⟨249391905601655473253863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1330090163208829190687269 249391905601655473253863)
                      ·
                        rfl

theorem cell23_485689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_485689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485689 prefixEnd_485689 := by exact prefixLift 485689
  have htrace : WordTrace (prefixWord ++ tailWord_485689) baseStart_485689 baseEnd_485689 := by
    simpa [prefixWord, tailWord_485689, baseEnd_485689] using wordTrace_append hprefix tailTrace_485689
  have hstable : (prefixWord ++ tailWord_485689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485689).length < 2 ^ (prefixWord ++ tailWord_485689).sum := by decide
  have hdescent : baseEnd_485689 < baseStart_485689 := by decide
  rcases family_descends (prefixWord ++ tailWord_485689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485732 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_485732 : Nat := 118140960795 + 485732 * 2 ^ 59
def prefixEnd_485732 : Nat := 4983230072969 + 3 ^ 40 * 485732 * 2
def baseEnd_485732 : Nat := 249413985269798805016165

theorem tailTrace_485732 : CollatzResearch.WordTrace tailWord_485732 prefixEnd_485732 249413985269798805016165 := by
  unfold tailWord_485732
  simp only [CollatzResearch.WordTrace]
  refine ⟨8858050738141697633105725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11810734317522263510807633 8858050738141697633105725)
  ·
    refine ⟨3321769026803136612414647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8858050738141697633105725 3321769026803136612414647)
    ·
      refine ⟨4982653540204704918621971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3321769026803136612414647 4982653540204704918621971)
      ·
        refine ⟨7473980310307057377932957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4982653540204704918621971 7473980310307057377932957)
        ·
          refine ⟨2802742616365146516724859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7473980310307057377932957 2802742616365146516724859)
          ·
            refine ⟨4204113924547719775087289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802742616365146516724859 4204113924547719775087289)
            ·
              refine ⟨3153085443410789831315467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4204113924547719775087289 3153085443410789831315467)
              ·
                refine ⟨4729628165116184746973201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3153085443410789831315467 4729628165116184746973201)
                ·
                  refine ⟨3547221123837138560229901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4729628165116184746973201 3547221123837138560229901)
                  ·
                    refine ⟨1330207921438926960086213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3547221123837138560229901 1330207921438926960086213)
                    ·
                      refine ⟨249413985269798805016165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1330207921438926960086213 249413985269798805016165)
                      ·
                        rfl

theorem cell23_485732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_485732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485732 prefixEnd_485732 := by exact prefixLift 485732
  have htrace : WordTrace (prefixWord ++ tailWord_485732) baseStart_485732 baseEnd_485732 := by
    simpa [prefixWord, tailWord_485732, baseEnd_485732] using wordTrace_append hprefix tailTrace_485732
  have hstable : (prefixWord ++ tailWord_485732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485732).length < 2 ^ (prefixWord ++ tailWord_485732).sum := by decide
  have hdescent : baseEnd_485732 < baseStart_485732 := by decide
  rcases family_descends (prefixWord ++ tailWord_485732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485799 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_485799 : Nat := 118140960795 + 485799 * 2 ^ 59
def prefixEnd_485799 : Nat := 4983230072969 + 3 ^ 40 * 485799 * 2
def baseEnd_485799 : Nat := 249448388473650042878357

theorem tailTrace_485799 : CollatzResearch.WordTrace tailWord_485799 prefixEnd_485799 249448388473650042878357 := by
  unfold tailWord_485799
  simp only [CollatzResearch.WordTrace]
  refine ⟨17718545167040665708900451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11812363444693777139266967 17718545167040665708900451)
  ·
    refine ⟨26577817750560998563350677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17718545167040665708900451 26577817750560998563350677)
    ·
      refine ⟨1245835207057546807657063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26577817750560998563350677 1245835207057546807657063)
      ·
        refine ⟨1868752810586320211485595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245835207057546807657063 1868752810586320211485595)
        ·
          refine ⟨2803129215879480317228393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868752810586320211485595 2803129215879480317228393)
          ·
            refine ⟨2102346911909610237921295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2803129215879480317228393 2102346911909610237921295)
            ·
              refine ⟨3153520367864415356881943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2102346911909610237921295 3153520367864415356881943)
              ·
                refine ⟨4730280551796623035322915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3153520367864415356881943 4730280551796623035322915)
                ·
                  refine ⟨7095420827694934552984373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4730280551796623035322915 7095420827694934552984373)
                  ·
                    refine ⟨665195702596400114342285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7095420827694934552984373 665195702596400114342285)
                    ·
                      refine ⟨249448388473650042878357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 665195702596400114342285 249448388473650042878357)
                      ·
                        rfl

theorem cell23_485799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_485799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485799 prefixEnd_485799 := by exact prefixLift 485799
  have htrace : WordTrace (prefixWord ++ tailWord_485799) baseStart_485799 baseEnd_485799 := by
    simpa [prefixWord, tailWord_485799, baseEnd_485799] using wordTrace_append hprefix tailTrace_485799
  have hstable : (prefixWord ++ tailWord_485799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485799).length < 2 ^ (prefixWord ++ tailWord_485799).sum := by decide
  have hdescent : baseEnd_485799 < baseStart_485799 := by decide
  rcases family_descends (prefixWord ++ tailWord_485799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485800 : List Nat := [2, 1, 6, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_485800 : Nat := 118140960795 + 485800 * 2 ^ 59
def prefixEnd_485800 : Nat := 4983230072969 + 3 ^ 40 * 485800 * 2
def baseEnd_485800 : Nat := 249448901954304538965853

theorem tailTrace_485800 : CollatzResearch.WordTrace tailWord_485800 prefixEnd_485800 249448901954304538965853 := by
  unfold tailWord_485800
  simp only [CollatzResearch.WordTrace]
  refine ⟨8859290820018521439843427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11812387760024695253124569 8859290820018521439843427)
  ·
    refine ⟨13288936230027782159765141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8859290820018521439843427 13288936230027782159765141)
    ·
      refine ⟨622918885782552288738991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13288936230027782159765141 622918885782552288738991)
      ·
        refine ⟨934378328673828433108487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622918885782552288738991 934378328673828433108487)
        ·
          refine ⟨1401567493010742649662731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934378328673828433108487 1401567493010742649662731)
          ·
            refine ⟨2102351239516113974494097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401567493010742649662731 2102351239516113974494097)
            ·
              refine ⟨1576763429637085480870573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102351239516113974494097 1576763429637085480870573)
              ·
                refine ⟨591286286113907055326465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1576763429637085480870573 591286286113907055326465)
                ·
                  refine ⟨443464714585430291494849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591286286113907055326465 443464714585430291494849)
                  ·
                    refine ⟨332598535939072718621137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 443464714585430291494849 332598535939072718621137)
                    ·
                      refine ⟨249448901954304538965853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 332598535939072718621137 249448901954304538965853)
                      ·
                        rfl

theorem cell23_485800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_485800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485800 prefixEnd_485800 := by exact prefixLift 485800
  have htrace : WordTrace (prefixWord ++ tailWord_485800) baseStart_485800 baseEnd_485800 := by
    simpa [prefixWord, tailWord_485800, baseEnd_485800] using wordTrace_append hprefix tailTrace_485800
  have hstable : (prefixWord ++ tailWord_485800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485800).length < 2 ^ (prefixWord ++ tailWord_485800).sum := by decide
  have hdescent : baseEnd_485800 < baseStart_485800 := by decide
  rcases family_descends (prefixWord ++ tailWord_485800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485866 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 3, 4]
def baseStart_485866 : Nat := 118140960795 + 485866 * 2 ^ 59
def prefixEnd_485866 : Nat := 4983230072969 + 3 ^ 40 * 485866 * 2
def baseEnd_485866 : Nat := 83160930559167093580183

theorem tailTrace_485866 : CollatzResearch.WordTrace tailWord_485866 prefixEnd_485866 83160930559167093580183 := by
  unfold tailWord_485866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4430247214449484037897363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11813992571865290767726301 4430247214449484037897363)
  ·
    refine ⟨6645370821674226056846045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4430247214449484037897363 6645370821674226056846045)
    ·
      refine ⟨2492014058127834771317267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6645370821674226056846045 2492014058127834771317267)
      ·
        refine ⟨3738021087191752156975901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2492014058127834771317267 3738021087191752156975901)
        ·
          refine ⟨1401757907696907058865963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3738021087191752156975901 1401757907696907058865963)
          ·
            refine ⟨2102636861545360588298945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401757907696907058865963 2102636861545360588298945)
            ·
              refine ⟨1576977646159020441224209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102636861545360588298945 1576977646159020441224209)
              ·
                refine ⟨1182733234619265330918157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576977646159020441224209 1182733234619265330918157)
                ·
                  refine ⟨443524962982224499094309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182733234619265330918157 443524962982224499094309)
                  ·
                    refine ⟨83160930559167093580183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 443524962982224499094309 83160930559167093580183)
                    ·
                      rfl

theorem cell23_485866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_485866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485866 prefixEnd_485866 := by exact prefixLift 485866
  have htrace : WordTrace (prefixWord ++ tailWord_485866) baseStart_485866 baseEnd_485866 := by
    simpa [prefixWord, tailWord_485866, baseEnd_485866] using wordTrace_append hprefix tailTrace_485866
  have hstable : (prefixWord ++ tailWord_485866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485866).length < 2 ^ (prefixWord ++ tailWord_485866).sum := by decide
  have hdescent : baseEnd_485866 < baseStart_485866 := by decide
  rcases family_descends (prefixWord ++ tailWord_485866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485882 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_485882 : Nat := 118140960795 + 485882 * 2 ^ 59
def prefixEnd_485882 : Nat := 4983230072969 + 3 ^ 40 * 485882 * 2
def baseEnd_485882 : Nat := 249491007367973218140475

theorem tailTrace_485882 : CollatzResearch.WordTrace tailWord_485882 prefixEnd_485882 249491007367973218140475 := by
  unfold tailWord_485882
  simp only [CollatzResearch.WordTrace]
  refine ⟨4430393106434992721042975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11814381617159980589447933 4430393106434992721042975)
  ·
    refine ⟨6645589659652489081564463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4430393106434992721042975 6645589659652489081564463)
    ·
      refine ⟨9968384489478733622346695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6645589659652489081564463 9968384489478733622346695)
      ·
        refine ⟨14952576734218100433520043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9968384489478733622346695 14952576734218100433520043)
        ·
          refine ⟨22428865101327150650280065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14952576734218100433520043 22428865101327150650280065)
          ·
            refine ⟨16821648825995362987710049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22428865101327150650280065 16821648825995362987710049)
            ·
              refine ⟨12616236619496522240782537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16821648825995362987710049 12616236619496522240782537)
              ·
                refine ⟨9462177464622391680586903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12616236619496522240782537 9462177464622391680586903)
                ·
                  refine ⟨14193266196933587520880355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9462177464622391680586903 14193266196933587520880355)
                  ·
                    refine ⟨21289899295400381281320533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14193266196933587520880355 21289899295400381281320533)
                    ·
                      refine ⟨249491007367973218140475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 21289899295400381281320533 249491007367973218140475)
                      ·
                        rfl

theorem cell23_485882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_485882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485882 prefixEnd_485882 := by exact prefixLift 485882
  have htrace : WordTrace (prefixWord ++ tailWord_485882) baseStart_485882 baseEnd_485882 := by
    simpa [prefixWord, tailWord_485882, baseEnd_485882] using wordTrace_append hprefix tailTrace_485882
  have hstable : (prefixWord ++ tailWord_485882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485882).length < 2 ^ (prefixWord ++ tailWord_485882).sum := by decide
  have hdescent : baseEnd_485882 < baseStart_485882 := by decide
  rcases family_descends (prefixWord ++ tailWord_485882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485900 : List Nat := [2, 2, 1, 2, 4, 2, 3, 2, 1, 4]
def baseStart_485900 : Nat := 118140960795 + 485900 * 2 ^ 59
def prefixEnd_485900 : Nat := 4983230072969 + 3 ^ 40 * 485900 * 2
def baseEnd_485900 : Nat := 83166750006584715905131

theorem tailTrace_485900 : CollatzResearch.WordTrace tailWord_485900 prefixEnd_485900 83166750006584715905131 := by
  unfold tailWord_485900
  simp only [CollatzResearch.WordTrace]
  refine ⟨8861114469837379979163577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11814819293116506638884769 8861114469837379979163577)
  ·
    refine ⟨6645835852378034984372683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8861114469837379979163577 6645835852378034984372683)
    ·
      refine ⟨9968753778567052476559025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6645835852378034984372683 9968753778567052476559025)
      ·
        refine ⟨7476565333925289357419269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9968753778567052476559025 7476565333925289357419269)
        ·
          refine ⟨1401856000110991754516113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7476565333925289357419269 1401856000110991754516113)
          ·
            refine ⟨1051392000083243815887085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1401856000110991754516113 1051392000083243815887085)
            ·
              refine ⟨394272000031216430957657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1051392000083243815887085 394272000031216430957657)
              ·
                refine ⟨295704000023412323218243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394272000031216430957657 295704000023412323218243)
                ·
                  refine ⟨443556000035118484827365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295704000023412323218243 443556000035118484827365)
                  ·
                    refine ⟨83166750006584715905131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 443556000035118484827365 83166750006584715905131)
                    ·
                      rfl

theorem cell23_485900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_485900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485900 prefixEnd_485900 := by exact prefixLift 485900
  have htrace : WordTrace (prefixWord ++ tailWord_485900) baseStart_485900 baseEnd_485900 := by
    simpa [prefixWord, tailWord_485900, baseEnd_485900] using wordTrace_append hprefix tailTrace_485900
  have hstable : (prefixWord ++ tailWord_485900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485900).length < 2 ^ (prefixWord ++ tailWord_485900).sum := by decide
  have hdescent : baseEnd_485900 < baseStart_485900 := by decide
  rcases family_descends (prefixWord ++ tailWord_485900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485909 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 3, 5]
def baseStart_485909 : Nat := 118140960795 + 485909 * 2 ^ 59
def prefixEnd_485909 : Nat := 4983230072969 + 3 ^ 40 * 485909 * 2
def baseEnd_485909 : Nat := 83168290448548204167617

theorem tailTrace_485909 : CollatzResearch.WordTrace tailWord_485909 prefixEnd_485909 83168290448548204167617 := by
  unfold tailWord_485909
  simp only [CollatzResearch.WordTrace]
  refine ⟨17722557196642154495404781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11815038131094769663603187 17722557196642154495404781)
  ·
    refine ⟨6645958948740807935776793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17722557196642154495404781 6645958948740807935776793)
    ·
      refine ⟨4984469211555605951832595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6645958948740807935776793 4984469211555605951832595)
      ·
        refine ⟨7476703817333408927748893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4984469211555605951832595 7476703817333408927748893)
        ·
          refine ⟨2803763931500028347905835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7476703817333408927748893 2803763931500028347905835)
          ·
            refine ⟨4205645897250042521858753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803763931500028347905835 4205645897250042521858753)
            ·
              refine ⟨3154234422937531891394065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4205645897250042521858753 3154234422937531891394065)
              ·
                refine ⟨2365675817203148918545549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3154234422937531891394065 2365675817203148918545549)
                ·
                  refine ⟨887128431451180844454581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2365675817203148918545549 887128431451180844454581)
                  ·
                    refine ⟨83168290448548204167617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 887128431451180844454581 83168290448548204167617)
                    ·
                      rfl

theorem cell23_485909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_485909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485909 prefixEnd_485909 := by exact prefixLift 485909
  have htrace : WordTrace (prefixWord ++ tailWord_485909) baseStart_485909 baseEnd_485909 := by
    simpa [prefixWord, tailWord_485909, baseEnd_485909] using wordTrace_append hprefix tailTrace_485909
  have hstable : (prefixWord ++ tailWord_485909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485909).length < 2 ^ (prefixWord ++ tailWord_485909).sum := by decide
  have hdescent : baseEnd_485909 < baseStart_485909 := by decide
  rcases family_descends (prefixWord ++ tailWord_485909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485939 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 1, 6]
def baseStart_485939 : Nat := 118140960795 + 485939 * 2 ^ 59
def prefixEnd_485939 : Nat := 4983230072969 + 3 ^ 40 * 485939 * 2
def baseEnd_485939 : Nat := 83173425255093165042571

theorem tailTrace_485939 : CollatzResearch.WordTrace tailWord_485939 prefixEnd_485939 83173425255093165042571 := by
  unfold tailWord_485939
  simp only [CollatzResearch.WordTrace]
  refine ⟨17723651386533469618996871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11815767591022313079331247 17723651386533469618996871)
  ·
    refine ⟨26585477079800204428495307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17723651386533469618996871 26585477079800204428495307)
    ·
      refine ⟨39878215619700306642742961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26585477079800204428495307 39878215619700306642742961)
      ·
        refine ⟨29908661714775229982057221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39878215619700306642742961 29908661714775229982057221)
        ·
          refine ⟨5607874071520355621635729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29908661714775229982057221 5607874071520355621635729)
          ·
            refine ⟨4205905553640266716226797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5607874071520355621635729 4205905553640266716226797)
            ·
              refine ⟨1577214582615100018585049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4205905553640266716226797 1577214582615100018585049)
              ·
                refine ⟨1182910936961325013938787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577214582615100018585049 1182910936961325013938787)
                ·
                  refine ⟨1774366405441987520908181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182910936961325013938787 1774366405441987520908181)
                  ·
                    refine ⟨83173425255093165042571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1774366405441987520908181 83173425255093165042571)
                    ·
                      rfl

theorem cell23_485939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 6].length) (baseStart_485939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485939 prefixEnd_485939 := by exact prefixLift 485939
  have htrace : WordTrace (prefixWord ++ tailWord_485939) baseStart_485939 baseEnd_485939 := by
    simpa [prefixWord, tailWord_485939, baseEnd_485939] using wordTrace_append hprefix tailTrace_485939
  have hstable : (prefixWord ++ tailWord_485939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485939).length < 2 ^ (prefixWord ++ tailWord_485939).sum := by decide
  have hdescent : baseEnd_485939 < baseStart_485939 := by decide
  rcases family_descends (prefixWord ++ tailWord_485939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485957 : List Nat := [1, 3, 1, 1, 1, 7, 2, 2, 1, 1, 3]
def baseStart_485957 : Nat := 118140960795 + 485957 * 2 ^ 59
def prefixEnd_485957 : Nat := 4983230072969 + 3 ^ 40 * 485957 * 2
def baseEnd_485957 : Nat := 249529518417060424702631

theorem tailTrace_485957 : CollatzResearch.WordTrace tailWord_485957 prefixEnd_485957 249529518417060424702631 := by
  unfold tailWord_485957
  simp only [CollatzResearch.WordTrace]
  refine ⟨17724307900468258693152125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11816205266978839128768083 17724307900468258693152125)
  ·
    refine ⟨6646615462675597009932047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17724307900468258693152125 6646615462675597009932047)
    ·
      refine ⟨9969923194013395514898071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6646615462675597009932047 9969923194013395514898071)
      ·
        refine ⟨14954884791020093272347107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9969923194013395514898071 14954884791020093272347107)
        ·
          refine ⟨22432327186530139908520661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14954884791020093272347107 22432327186530139908520661)
          ·
            refine ⟨525757668434300154105953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 22432327186530139908520661 525757668434300154105953)
            ·
              refine ⟨394318251325725115579465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525757668434300154105953 394318251325725115579465)
              ·
                refine ⟨295738688494293836684599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394318251325725115579465 295738688494293836684599)
                ·
                  refine ⟨443608032741440755026899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295738688494293836684599 443608032741440755026899)
                  ·
                    refine ⟨665412049112161132540349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 443608032741440755026899 665412049112161132540349)
                    ·
                      refine ⟨249529518417060424702631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 665412049112161132540349 249529518417060424702631)
                      ·
                        rfl

theorem cell23_485957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 1, 1, 3].length) (baseStart_485957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485957 prefixEnd_485957 := by exact prefixLift 485957
  have htrace : WordTrace (prefixWord ++ tailWord_485957) baseStart_485957 baseEnd_485957 := by
    simpa [prefixWord, tailWord_485957, baseEnd_485957] using wordTrace_append hprefix tailTrace_485957
  have hstable : (prefixWord ++ tailWord_485957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485957).length < 2 ^ (prefixWord ++ tailWord_485957).sum := by decide
  have hdescent : baseEnd_485957 < baseStart_485957 := by decide
  rcases family_descends (prefixWord ++ tailWord_485957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485966 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_485966 : Nat := 118140960795 + 485966 * 2 ^ 59
def prefixEnd_485966 : Nat := 4983230072969 + 3 ^ 40 * 485966 * 2
def baseEnd_485966 : Nat := 249534139742950889490089

theorem tailTrace_485966 : CollatzResearch.WordTrace tailWord_485966 prefixEnd_485966 249534139742950889490089 := by
  unfold tailWord_485966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2215579519679456653778719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11816424104957102153486501 2215579519679456653778719)
  ·
    refine ⟨3323369279519184980668079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2215579519679456653778719 3323369279519184980668079)
    ·
      refine ⟨4985053919278777471002119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3323369279519184980668079 4985053919278777471002119)
      ·
        refine ⟨7477580878918166206503179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4985053919278777471002119 7477580878918166206503179)
        ·
          refine ⟨11216371318377249309754769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7477580878918166206503179 11216371318377249309754769)
          ·
            refine ⟨8412278488782936982316077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11216371318377249309754769 8412278488782936982316077)
            ·
              refine ⟨3154604433293601368368529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8412278488782936982316077 3154604433293601368368529)
              ·
                refine ⟨2365953324970201026276397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3154604433293601368368529 2365953324970201026276397)
                ·
                  refine ⟨887232496863825384853649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2365953324970201026276397 887232496863825384853649)
                  ·
                    refine ⟨665424372647869038640237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 887232496863825384853649 665424372647869038640237)
                    ·
                      refine ⟨249534139742950889490089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 665424372647869038640237 249534139742950889490089)
                      ·
                        rfl

theorem cell23_485966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_485966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485966 prefixEnd_485966 := by exact prefixLift 485966
  have htrace : WordTrace (prefixWord ++ tailWord_485966) baseStart_485966 baseEnd_485966 := by
    simpa [prefixWord, tailWord_485966, baseEnd_485966] using wordTrace_append hprefix tailTrace_485966
  have hstable : (prefixWord ++ tailWord_485966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485966).length < 2 ^ (prefixWord ++ tailWord_485966).sum := by decide
  have hdescent : baseEnd_485966 < baseStart_485966 := by decide
  rcases family_descends (prefixWord ++ tailWord_485966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485969 : List Nat := [1, 2, 2, 1, 3, 3, 3, 8]
def baseStart_485969 : Nat := 118140960795 + 485969 * 2 ^ 59
def prefixEnd_485969 : Nat := 4983230072969 + 3 ^ 40 * 485969 * 2
def baseEnd_485969 : Nat := 9242062229070902879725

theorem tailTrace_485969 : CollatzResearch.WordTrace tailWord_485969 prefixEnd_485969 9242062229070902879725 := by
  unfold tailWord_485969
  simp only [CollatzResearch.WordTrace]
  refine ⟨17724745576424784742588961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11816497050949856495059307 17724745576424784742588961)
  ·
    refine ⟨13293559182318588556941721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17724745576424784742588961 13293559182318588556941721)
    ·
      refine ⟨9970169386738941417706291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13293559182318588556941721 9970169386738941417706291)
      ·
        refine ⟨14955254080108412126559437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9970169386738941417706291 14955254080108412126559437)
        ·
          refine ⟨5608220280040654547459789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14955254080108412126559437 5608220280040654547459789)
          ·
            refine ⟨2103082605015245455297421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5608220280040654547459789 2103082605015245455297421)
            ·
              refine ⟨788655976880717045736533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2103082605015245455297421 788655976880717045736533)
              ·
                refine ⟨9242062229070902879725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 788655976880717045736533 9242062229070902879725)
                ·
                  rfl

theorem cell23_485969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 8].length) (baseStart_485969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485969 prefixEnd_485969 := by exact prefixLift 485969
  have htrace : WordTrace (prefixWord ++ tailWord_485969) baseStart_485969 baseEnd_485969 := by
    simpa [prefixWord, tailWord_485969, baseEnd_485969] using wordTrace_append hprefix tailTrace_485969
  have hstable : (prefixWord ++ tailWord_485969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485969).length < 2 ^ (prefixWord ++ tailWord_485969).sum := by decide
  have hdescent : baseEnd_485969 < baseStart_485969 := by decide
  rcases family_descends (prefixWord ++ tailWord_485969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485996 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 3]
def baseStart_485996 : Nat := 118140960795 + 485996 * 2 ^ 59
def prefixEnd_485996 : Nat := 4983230072969 + 3 ^ 40 * 485996 * 2
def baseEnd_485996 : Nat := 249549544162585772114951

theorem tailTrace_485996 : CollatzResearch.WordTrace tailWord_485996 prefixEnd_485996 249549544162585772114951 := by
  unfold tailWord_485996
  simp only [CollatzResearch.WordTrace]
  refine ⟨8862865173663484176910921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11817153564884645569214561 8862865173663484176910921)
  ·
    refine ⟨6647148880247613132683191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8862865173663484176910921 6647148880247613132683191)
    ·
      refine ⟨9970723320371419699024787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6647148880247613132683191 9970723320371419699024787)
      ·
        refine ⟨14956084980557129548537181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9970723320371419699024787 14956084980557129548537181)
        ·
          refine ⟨5608531867708923580701443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14956084980557129548537181 5608531867708923580701443)
          ·
            refine ⟨8412797801563385371052165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5608531867708923580701443 8412797801563385371052165)
            ·
              refine ⟨1577399587793134757072281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8412797801563385371052165 1577399587793134757072281)
              ·
                refine ⟨1183049690844851067804211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577399587793134757072281 1183049690844851067804211)
                ·
                  refine ⟨1774574536267276601706317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183049690844851067804211 1774574536267276601706317)
                  ·
                    refine ⟨665465451100228725639869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1774574536267276601706317 665465451100228725639869)
                    ·
                      refine ⟨249549544162585772114951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 665465451100228725639869 249549544162585772114951)
                      ·
                        rfl

theorem cell23_485996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_485996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485996 prefixEnd_485996 := by exact prefixLift 485996
  have htrace : WordTrace (prefixWord ++ tailWord_485996) baseStart_485996 baseEnd_485996 := by
    simpa [prefixWord, tailWord_485996, baseEnd_485996] using wordTrace_append hprefix tailTrace_485996
  have hstable : (prefixWord ++ tailWord_485996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485996).length < 2 ^ (prefixWord ++ tailWord_485996).sum := by decide
  have hdescent : baseEnd_485996 < baseStart_485996 := by decide
  rcases family_descends (prefixWord ++ tailWord_485996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485997 : List Nat := [1, 5, 1, 1, 3, 1, 1, 5, 1, 2, 2]
def baseStart_485997 : Nat := 118140960795 + 485997 * 2 ^ 59
def prefixEnd_485997 : Nat := 4983230072969 + 3 ^ 40 * 485997 * 2
def baseEnd_485997 : Nat := 249550057643240268202447

theorem tailTrace_485997 : CollatzResearch.WordTrace tailWord_485997 prefixEnd_485997 249550057643240268202447 := by
  unfold tailWord_485997
  simp only [CollatzResearch.WordTrace]
  refine ⟨17725766820323345524608245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11817177880215563683072163 17725766820323345524608245)
  ·
    refine ⟨1661790639405313642932023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17725766820323345524608245 1661790639405313642932023)
    ·
      refine ⟨2492685959107970464398035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1661790639405313642932023 2492685959107970464398035)
      ·
        refine ⟨3739028938661955696597053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2492685959107970464398035 3739028938661955696597053)
        ·
          refine ⟨1402135851998233386223895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3739028938661955696597053 1402135851998233386223895)
          ·
            refine ⟨2103203777997350079335843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402135851998233386223895 2103203777997350079335843)
            ·
              refine ⟨3154805666996025119003765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103203777997350079335843 3154805666996025119003765)
              ·
                refine ⟨295763031280877354906603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3154805666996025119003765 295763031280877354906603)
                ·
                  refine ⟨443644546921316032359905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295763031280877354906603 443644546921316032359905)
                  ·
                    refine ⟨332733410190987024269929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 443644546921316032359905 332733410190987024269929)
                    ·
                      refine ⟨249550057643240268202447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 332733410190987024269929 249550057643240268202447)
                      ·
                        rfl

theorem cell23_485997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_485997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_485997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_485997 prefixEnd_485997 := by exact prefixLift 485997
  have htrace : WordTrace (prefixWord ++ tailWord_485997) baseStart_485997 baseEnd_485997 := by
    simpa [prefixWord, tailWord_485997, baseEnd_485997] using wordTrace_append hprefix tailTrace_485997
  have hstable : (prefixWord ++ tailWord_485997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485997).length < 2 ^ (prefixWord ++ tailWord_485997).sum := by decide
  have hdescent : baseEnd_485997 < baseStart_485997 := by decide
  rcases family_descends (prefixWord ++ tailWord_485997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486019 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 4]
def baseStart_486019 : Nat := 118140960795 + 486019 * 2 ^ 59
def prefixEnd_486019 : Nat := 4983230072969 + 3 ^ 40 * 486019 * 2
def baseEnd_486019 : Nat := 249561354217639182127345

theorem tailTrace_486019 : CollatzResearch.WordTrace tailWord_486019 prefixEnd_486019 249561354217639182127345 := by
  unfold tailWord_486019
  simp only [CollatzResearch.WordTrace]
  refine ⟨17726569226243643281909111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11817712817495762187939407 17726569226243643281909111)
  ·
    refine ⟨26589853839365464922863667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17726569226243643281909111 26589853839365464922863667)
    ·
      refine ⟨39884780759048197384295501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26589853839365464922863667 39884780759048197384295501)
      ·
        refine ⟨14956792784643074019110813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39884780759048197384295501 14956792784643074019110813)
        ·
          refine ⟨5608797294241152757166555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14956792784643074019110813 5608797294241152757166555)
          ·
            refine ⟨8413195941361729135749833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5608797294241152757166555 8413195941361729135749833)
            ·
              refine ⟨6309896956021296851812375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8413195941361729135749833 6309896956021296851812375)
              ·
                refine ⟨9464845434031945277718563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309896956021296851812375 9464845434031945277718563)
                ·
                  refine ⟨14197268151047917916577845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9464845434031945277718563 14197268151047917916577845)
                  ·
                    refine ⟨1330993889160742304679173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14197268151047917916577845 1330993889160742304679173)
                    ·
                      refine ⟨249561354217639182127345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1330993889160742304679173 249561354217639182127345)
                      ·
                        rfl

theorem cell23_486019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_486019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486019 prefixEnd_486019 := by exact prefixLift 486019
  have htrace : WordTrace (prefixWord ++ tailWord_486019) baseStart_486019 baseEnd_486019 := by
    simpa [prefixWord, tailWord_486019, baseEnd_486019] using wordTrace_append hprefix tailTrace_486019
  have hstable : (prefixWord ++ tailWord_486019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486019).length < 2 ^ (prefixWord ++ tailWord_486019).sum := by decide
  have hdescent : baseEnd_486019 < baseStart_486019 := by decide
  rcases family_descends (prefixWord ++ tailWord_486019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486040 : List Nat := [2, 1, 2, 4, 1, 1, 4, 2, 1, 3, 2]
def baseStart_486040 : Nat := 118140960795 + 486040 * 2 ^ 59
def prefixEnd_486040 : Nat := 4983230072969 + 3 ^ 40 * 486040 * 2
def baseEnd_486040 : Nat := 249572137311383599964749

theorem tailTrace_486040 : CollatzResearch.WordTrace tailWord_486040 prefixEnd_486040 249572137311383599964749 := by
  unfold tailWord_486040
  simp only [CollatzResearch.WordTrace]
  refine ⟨8863667579583781934211787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11818223439445042578949049 8863667579583781934211787)
  ·
    refine ⟨13295501369375672901317681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8863667579583781934211787 13295501369375672901317681)
    ·
      refine ⟨9971626027031754675988261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13295501369375672901317681 9971626027031754675988261)
      ·
        refine ⟨1869679880068454001747799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9971626027031754675988261 1869679880068454001747799)
        ·
          refine ⟨2804519820102681002621699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869679880068454001747799 2804519820102681002621699)
          ·
            refine ⟨4206779730154021503932549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804519820102681002621699 4206779730154021503932549)
            ·
              refine ⟨788771199403879031987353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4206779730154021503932549 788771199403879031987353)
              ·
                refine ⟨591578399552909273990515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788771199403879031987353 591578399552909273990515)
                ·
                  refine ⟨887367599329363910985773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591578399552909273990515 887367599329363910985773)
                  ·
                    refine ⟨332762849748511466619665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 887367599329363910985773 332762849748511466619665)
                    ·
                      refine ⟨249572137311383599964749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 332762849748511466619665 249572137311383599964749)
                      ·
                        rfl

theorem cell23_486040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_486040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486040 prefixEnd_486040 := by exact prefixLift 486040
  have htrace : WordTrace (prefixWord ++ tailWord_486040) baseStart_486040 baseEnd_486040 := by
    simpa [prefixWord, tailWord_486040, baseEnd_486040] using wordTrace_append hprefix tailTrace_486040
  have hstable : (prefixWord ++ tailWord_486040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486040).length < 2 ^ (prefixWord ++ tailWord_486040).sum := by decide
  have hdescent : baseEnd_486040 < baseStart_486040 := by decide
  rcases family_descends (prefixWord ++ tailWord_486040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486081 : List Nat := [1, 2, 6, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_486081 : Nat := 118140960795 + 486081 * 2 ^ 59
def prefixEnd_486081 : Nat := 4983230072969 + 3 ^ 40 * 486081 * 2
def baseEnd_486081 : Nat := 249593190018217939552061

theorem tailTrace_486081 : CollatzResearch.WordTrace tailWord_486081 prefixEnd_486081 249593190018217939552061 := by
  unfold tailWord_486081
  simp only [CollatzResearch.WordTrace]
  refine ⟨17728830552019027870666097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11819220368012685247110731 17728830552019027870666097)
  ·
    refine ⟨13296622914014270902999573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17728830552019027870666097 13296622914014270902999573)
    ·
      refine ⟨623279199094418948578105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13296622914014270902999573 623279199094418948578105)
      ·
        refine ⟨467459399320814211433579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623279199094418948578105 467459399320814211433579)
        ·
          refine ⟨701189098981221317150369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467459399320814211433579 701189098981221317150369)
          ·
            refine ⟨525891824235915987862777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701189098981221317150369 525891824235915987862777)
            ·
              refine ⟨394418868176936990897083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525891824235915987862777 394418868176936990897083)
              ·
                refine ⟨591628302265405486345625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394418868176936990897083 591628302265405486345625)
                ·
                  refine ⟨443721226699054114759219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591628302265405486345625 443721226699054114759219)
                  ·
                    refine ⟨665581840048581172138829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 443721226699054114759219 665581840048581172138829)
                    ·
                      refine ⟨249593190018217939552061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 665581840048581172138829 249593190018217939552061)
                      ·
                        rfl

theorem cell23_486081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_486081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486081 prefixEnd_486081 := by exact prefixLift 486081
  have htrace : WordTrace (prefixWord ++ tailWord_486081) baseStart_486081 baseEnd_486081 := by
    simpa [prefixWord, tailWord_486081, baseEnd_486081] using wordTrace_append hprefix tailTrace_486081
  have hstable : (prefixWord ++ tailWord_486081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486081).length < 2 ^ (prefixWord ++ tailWord_486081).sum := by decide
  have hdescent : baseEnd_486081 < baseStart_486081 := by decide
  rcases family_descends (prefixWord ++ tailWord_486081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486116 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_486116 : Nat := 118140960795 + 486116 * 2 ^ 59
def prefixEnd_486116 : Nat := 4983230072969 + 3 ^ 40 * 486116 * 2
def baseEnd_486116 : Nat := 249611161841125302614399

theorem tailTrace_486116 : CollatzResearch.WordTrace tailWord_486116 prefixEnd_486116 249611161841125302614399 := by
  unfold tailWord_486116
  simp only [CollatzResearch.WordTrace]
  refine ⟨8865053553446114424095101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11820071404594819232126801 8865053553446114424095101)
  ·
    refine ⟨3324395082542292909035663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8865053553446114424095101 3324395082542292909035663)
    ·
      refine ⟨4986592623813439363553495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3324395082542292909035663 4986592623813439363553495)
      ·
        refine ⟨7479888935720159045330243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4986592623813439363553495 7479888935720159045330243)
        ·
          refine ⟨11219833403580238567995365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7479888935720159045330243 11219833403580238567995365)
          ·
            refine ⟨2103718763171294731499131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11219833403580238567995365 2103718763171294731499131)
            ·
              refine ⟨3155578144756942097248697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103718763171294731499131 3155578144756942097248697)
              ·
                refine ⟨2366683608567706572936523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3155578144756942097248697 2366683608567706572936523)
                ·
                  refine ⟨3550025412851559859404785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366683608567706572936523 3550025412851559859404785)
                  ·
                    refine ⟨2662519059638669894553589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3550025412851559859404785 2662519059638669894553589)
                    ·
                      refine ⟨249611161841125302614399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2662519059638669894553589 249611161841125302614399)
                      ·
                        rfl

theorem cell23_486116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_486116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486116 prefixEnd_486116 := by exact prefixLift 486116
  have htrace : WordTrace (prefixWord ++ tailWord_486116) baseStart_486116 baseEnd_486116 := by
    simpa [prefixWord, tailWord_486116, baseEnd_486116] using wordTrace_append hprefix tailTrace_486116
  have hstable : (prefixWord ++ tailWord_486116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486116).length < 2 ^ (prefixWord ++ tailWord_486116).sum := by decide
  have hdescent : baseEnd_486116 < baseStart_486116 := by decide
  rcases family_descends (prefixWord ++ tailWord_486116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486220 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 1, 5, 2]
def baseStart_486220 : Nat := 118140960795 + 486220 * 2 ^ 59
def prefixEnd_486220 : Nat := 4983230072969 + 3 ^ 40 * 486220 * 2
def baseEnd_486220 : Nat := 249664563829192895713921

theorem tailTrace_486220 : CollatzResearch.WordTrace tailWord_486220 prefixEnd_486220 249664563829192895713921 := by
  unfold tailWord_486220
  simp only [CollatzResearch.WordTrace]
  refine ⟨8866950149257727304988057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11822600199010303073317409 8866950149257727304988057)
  ·
    refine ⟨6650212611943295478741043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8866950149257727304988057 6650212611943295478741043)
    ·
      refine ⟨9975318917914943218111565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6650212611943295478741043 9975318917914943218111565)
      ·
        refine ⟨3740744594218103706791837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9975318917914943218111565 3740744594218103706791837)
        ·
          refine ⟨1402779222831788890046939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3740744594218103706791837 1402779222831788890046939)
          ·
            refine ⟨2104168834247683335070409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402779222831788890046939 2104168834247683335070409)
            ·
              refine ⟨1578126625685762501302807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2104168834247683335070409 1578126625685762501302807)
              ·
                refine ⟨2367189938528643751954211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578126625685762501302807 2367189938528643751954211)
                ·
                  refine ⟨3550784907792965627931317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367189938528643751954211 3550784907792965627931317)
                  ·
                    refine ⟨332886085105590527618561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3550784907792965627931317 332886085105590527618561)
                    ·
                      refine ⟨249664563829192895713921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 332886085105590527618561 249664563829192895713921)
                      ·
                        rfl

theorem cell23_486220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_486220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486220 prefixEnd_486220 := by exact prefixLift 486220
  have htrace : WordTrace (prefixWord ++ tailWord_486220) baseStart_486220 baseEnd_486220 := by
    simpa [prefixWord, tailWord_486220, baseEnd_486220] using wordTrace_append hprefix tailTrace_486220
  have hstable : (prefixWord ++ tailWord_486220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486220).length < 2 ^ (prefixWord ++ tailWord_486220).sum := by decide
  have hdescent : baseEnd_486220 < baseStart_486220 := by decide
  rcases family_descends (prefixWord ++ tailWord_486220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486221 : List Nat := [1, 6, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_486221 : Nat := 118140960795 + 486221 * 2 ^ 59
def prefixEnd_486221 : Nat := 4983230072969 + 3 ^ 40 * 486221 * 2
def baseEnd_486221 : Nat := 83221692436615797267139

theorem tailTrace_486221 : CollatzResearch.WordTrace tailWord_486221 prefixEnd_486221 83221692436615797267139 := by
  unfold tailWord_486221
  simp only [CollatzResearch.WordTrace]
  refine ⟨17733936771511831780762517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11822624514341221187175011 17733936771511831780762517)
  ·
    refine ⟨831278286164617114723243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17733936771511831780762517 831278286164617114723243)
    ·
      refine ⟨1246917429246925672084865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 831278286164617114723243 1246917429246925672084865)
      ·
        refine ⟨935188071935194254063649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1246917429246925672084865 935188071935194254063649)
        ·
          refine ⟨701391053951395690547737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 935188071935194254063649 701391053951395690547737)
          ·
            refine ⟨526043290463546767910803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701391053951395690547737 526043290463546767910803)
            ·
              refine ⟨789064935695320151866205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526043290463546767910803 789064935695320151866205)
              ·
                refine ⟨295899350885745056949827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 789064935695320151866205 295899350885745056949827)
                ·
                  refine ⟨443849026328617585424741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295899350885745056949827 443849026328617585424741)
                  ·
                    refine ⟨83221692436615797267139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 443849026328617585424741 83221692436615797267139)
                    ·
                      rfl

theorem cell23_486221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_486221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486221 prefixEnd_486221 := by exact prefixLift 486221
  have htrace : WordTrace (prefixWord ++ tailWord_486221) baseStart_486221 baseEnd_486221 := by
    simpa [prefixWord, tailWord_486221, baseEnd_486221] using wordTrace_append hprefix tailTrace_486221
  have hstable : (prefixWord ++ tailWord_486221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486221).length < 2 ^ (prefixWord ++ tailWord_486221).sum := by decide
  have hdescent : baseEnd_486221 < baseStart_486221 := by decide
  rcases family_descends (prefixWord ++ tailWord_486221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486253 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_486253 : Nat := 118140960795 + 486253 * 2 ^ 59
def prefixEnd_486253 : Nat := 4983230072969 + 3 ^ 40 * 486253 * 2
def baseEnd_486253 : Nat := 249681508690791266601269

theorem tailTrace_486253 : CollatzResearch.WordTrace tailWord_486253 prefixEnd_486253 249681508690791266601269 := by
  unfold tailWord_486253
  simp only [CollatzResearch.WordTrace]
  refine ⟨17735103907395901245927413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11823402604930600830618275 17735103907395901245927413)
  ·
    refine ⟨1662665991318365741805695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17735103907395901245927413 1662665991318365741805695)
    ·
      refine ⟨2493998986977548612708543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1662665991318365741805695 2493998986977548612708543)
      ·
        refine ⟨3740998480466322919062815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2493998986977548612708543 3740998480466322919062815)
        ·
          refine ⟨5611497720699484378594223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3740998480466322919062815 5611497720699484378594223)
          ·
            refine ⟨8417246581049226567891335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5611497720699484378594223 8417246581049226567891335)
            ·
              refine ⟨12625869871573839851837003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8417246581049226567891335 12625869871573839851837003)
              ·
                refine ⟨18938804807360759777755505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12625869871573839851837003 18938804807360759777755505)
                ·
                  refine ⟨14204103605520569833316629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18938804807360759777755505 14204103605520569833316629)
                  ·
                    refine ⟨665817356508776710936717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14204103605520569833316629 665817356508776710936717)
                    ·
                      refine ⟨249681508690791266601269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 665817356508776710936717 249681508690791266601269)
                      ·
                        rfl

theorem cell23_486253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_486253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486253 prefixEnd_486253 := by exact prefixLift 486253
  have htrace : WordTrace (prefixWord ++ tailWord_486253) baseStart_486253 baseEnd_486253 := by
    simpa [prefixWord, tailWord_486253, baseEnd_486253] using wordTrace_append hprefix tailTrace_486253
  have hstable : (prefixWord ++ tailWord_486253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486253).length < 2 ^ (prefixWord ++ tailWord_486253).sum := by decide
  have hdescent : baseEnd_486253 < baseStart_486253 := by decide
  rcases family_descends (prefixWord ++ tailWord_486253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486256 : List Nat := [2, 1, 1, 1, 4, 1, 3, 10]
def baseStart_486256 : Nat := 118140960795 + 486256 * 2 ^ 59
def prefixEnd_486256 : Nat := 4983230072969 + 3 ^ 40 * 486256 * 2
def baseEnd_486256 : Nat := 9247520338250176106065

theorem tailTrace_486256 : CollatzResearch.WordTrace tailWord_486256 prefixEnd_486256 9247520338250176106065 := by
  unfold tailWord_486256
  simp only [CollatzResearch.WordTrace]
  refine ⟨8867606663192516379143311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11823475550923355172191081 8867606663192516379143311)
  ·
    refine ⟨13301409994788774568714967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8867606663192516379143311 13301409994788774568714967)
    ·
      refine ⟨19952114992183161853072451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13301409994788774568714967 19952114992183161853072451)
      ·
        refine ⟨29928172488274742779608677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19952114992183161853072451 29928172488274742779608677)
        ·
          refine ⟨5611532341551514271176627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29928172488274742779608677 5611532341551514271176627)
          ·
            refine ⟨8417298512327271406764941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5611532341551514271176627 8417298512327271406764941)
            ·
              refine ⟨3156486942122726777536853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8417298512327271406764941 3156486942122726777536853)
              ·
                refine ⟨9247520338250176106065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3156486942122726777536853 9247520338250176106065)
                ·
                  rfl

theorem cell23_486256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 10].length) (baseStart_486256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486256 prefixEnd_486256 := by exact prefixLift 486256
  have htrace : WordTrace (prefixWord ++ tailWord_486256) baseStart_486256 baseEnd_486256 := by
    simpa [prefixWord, tailWord_486256, baseEnd_486256] using wordTrace_append hprefix tailTrace_486256
  have hstable : (prefixWord ++ tailWord_486256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486256).length < 2 ^ (prefixWord ++ tailWord_486256).sum := by decide
  have hdescent : baseEnd_486256 < baseStart_486256 := by decide
  rcases family_descends (prefixWord ++ tailWord_486256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486280 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_486280 : Nat := 118140960795 + 486280 * 2 ^ 59
def prefixEnd_486280 : Nat := 4983230072969 + 3 ^ 40 * 486280 * 2
def baseEnd_486280 : Nat := 249695372668462660963645

theorem tailTrace_486280 : CollatzResearch.WordTrace tailWord_486280 prefixEnd_486280 249695372668462660963645 := by
  unfold tailWord_486280
  simp only [CollatzResearch.WordTrace]
  refine ⟨8868044339149042428580147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11824059118865389904773529 8868044339149042428580147)
  ·
    refine ⟨13302066508723563642870221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8868044339149042428580147 13302066508723563642870221)
    ·
      refine ⟨4988274940771336366076333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13302066508723563642870221 4988274940771336366076333)
      ·
        refine ⟨1870603102789251137278625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4988274940771336366076333 1870603102789251137278625)
        ·
          refine ⟨1402952327091938352958969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1870603102789251137278625 1402952327091938352958969)
          ·
            refine ⟨1052214245318953764719227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1402952327091938352958969 1052214245318953764719227)
            ·
              refine ⟨1578321367978430647078841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052214245318953764719227 1578321367978430647078841)
              ·
                refine ⟨1183741025983822985309131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1578321367978430647078841 1183741025983822985309131)
                ·
                  refine ⟨1775611538975734477963697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183741025983822985309131 1775611538975734477963697)
                  ·
                    refine ⟨1331708654231800858472773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1775611538975734477963697 1331708654231800858472773)
                    ·
                      refine ⟨249695372668462660963645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1331708654231800858472773 249695372668462660963645)
                      ·
                        rfl

theorem cell23_486280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_486280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486280 prefixEnd_486280 := by exact prefixLift 486280
  have htrace : WordTrace (prefixWord ++ tailWord_486280) baseStart_486280 baseEnd_486280 := by
    simpa [prefixWord, tailWord_486280, baseEnd_486280] using wordTrace_append hprefix tailTrace_486280
  have hstable : (prefixWord ++ tailWord_486280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486280).length < 2 ^ (prefixWord ++ tailWord_486280).sum := by decide
  have hdescent : baseEnd_486280 < baseStart_486280 := by decide
  rcases family_descends (prefixWord ++ tailWord_486280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486283 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 3]
def baseStart_486283 : Nat := 118140960795 + 486283 * 2 ^ 59
def prefixEnd_486283 : Nat := 4983230072969 + 3 ^ 40 * 486283 * 2
def baseEnd_486283 : Nat := 249696913110426149226131

theorem tailTrace_486283 : CollatzResearch.WordTrace tailWord_486283 prefixEnd_486283 249696913110426149226131 := by
  unfold tailWord_486283
  simp only [CollatzResearch.WordTrace]
  refine ⟨17736198097287216369519503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11824132064858144246346335 17736198097287216369519503)
  ·
    refine ⟨26604297145930824554279255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17736198097287216369519503 26604297145930824554279255)
    ·
      refine ⟨39906445718896236831418883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26604297145930824554279255 39906445718896236831418883)
      ·
        refine ⟨59859668578344355247128325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39906445718896236831418883 59859668578344355247128325)
        ·
          refine ⟨11223687858439566608836561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59859668578344355247128325 11223687858439566608836561)
          ·
            refine ⟨8417765893829674956627421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11223687858439566608836561 8417765893829674956627421)
            ·
              refine ⟨3156662210186128108735283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8417765893829674956627421 3156662210186128108735283)
              ·
                refine ⟨4734993315279192163102925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3156662210186128108735283 4734993315279192163102925)
                ·
                  refine ⟨1775622493229697061163597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4734993315279192163102925 1775622493229697061163597)
                  ·
                    refine ⟨665858434961136397936349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1775622493229697061163597 665858434961136397936349)
                    ·
                      refine ⟨249696913110426149226131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 665858434961136397936349 249696913110426149226131)
                      ·
                        rfl

theorem cell23_486283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 3].length) (baseStart_486283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486283 prefixEnd_486283 := by exact prefixLift 486283
  have htrace : WordTrace (prefixWord ++ tailWord_486283) baseStart_486283 baseEnd_486283 := by
    simpa [prefixWord, tailWord_486283, baseEnd_486283] using wordTrace_append hprefix tailTrace_486283
  have hstable : (prefixWord ++ tailWord_486283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486283).length < 2 ^ (prefixWord ++ tailWord_486283).sum := by decide
  have hdescent : baseEnd_486283 < baseStart_486283 := by decide
  rcases family_descends (prefixWord ++ tailWord_486283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486290 : List Nat := [3, 2, 3, 2, 3, 10]
def baseStart_486290 : Nat := 118140960795 + 486290 * 2 ^ 59
def prefixEnd_486290 : Nat := 4983230072969 + 3 ^ 40 * 486290 * 2
def baseEnd_486290 : Nat := 1027574104835422312093

theorem tailTrace_486290 : CollatzResearch.WordTrace tailWord_486290 prefixEnd_486290 1027574104835422312093 := by
  unfold tailWord_486290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4434113352065464141256081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11824302272174571043349549 4434113352065464141256081)
  ·
    refine ⟨3325585014049098105942061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4434113352065464141256081 3325585014049098105942061)
    ·
      refine ⟨1247094380268411789728273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3325585014049098105942061 1247094380268411789728273)
      ·
        refine ⟨935320785201308842296205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1247094380268411789728273 935320785201308842296205)
        ·
          refine ⟨350745294450490815861077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 935320785201308842296205 350745294450490815861077)
          ·
            refine ⟨1027574104835422312093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 350745294450490815861077 1027574104835422312093)
            ·
              rfl

theorem cell23_486290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 10].length) (baseStart_486290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486290 prefixEnd_486290 := by exact prefixLift 486290
  have htrace : WordTrace (prefixWord ++ tailWord_486290) baseStart_486290 baseEnd_486290 := by
    simpa [prefixWord, tailWord_486290, baseEnd_486290] using wordTrace_append hprefix tailTrace_486290
  have hstable : (prefixWord ++ tailWord_486290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486290).length < 2 ^ (prefixWord ++ tailWord_486290).sum := by decide
  have hdescent : baseEnd_486290 < baseStart_486290 := by decide
  rcases family_descends (prefixWord ++ tailWord_486290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486303 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 2, 7]
def baseStart_486303 : Nat := 118140960795 + 486303 * 2 ^ 59
def prefixEnd_486303 : Nat := 4983230072969 + 3 ^ 40 * 486303 * 2
def baseEnd_486303 : Nat := 83235727574505356992013

theorem tailTrace_486303 : CollatzResearch.WordTrace tailWord_486303 prefixEnd_486303 83235727574505356992013 := by
  unfold tailWord_486303
  simp only [CollatzResearch.WordTrace]
  refine ⟨17736927557214759785247563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11824618371476506523498375 17736927557214759785247563)
  ·
    refine ⟨26605391335822139677871345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17736927557214759785247563 26605391335822139677871345)
    ·
      refine ⟨19954043501866604758403509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26605391335822139677871345 19954043501866604758403509)
      ·
        refine ⟨1870691578299994196100329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19954043501866604758403509 1870691578299994196100329)
        ·
          refine ⟨1403018683724995647075247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1870691578299994196100329 1403018683724995647075247)
          ·
            refine ⟨2104528025587493470612871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403018683724995647075247 2104528025587493470612871)
            ·
              refine ⟨3156792038381240205919307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2104528025587493470612871 3156792038381240205919307)
              ·
                refine ⟨4735188057571860308878961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3156792038381240205919307 4735188057571860308878961)
                ·
                  refine ⟨3551391043178895231659221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4735188057571860308878961 3551391043178895231659221)
                  ·
                    refine ⟨83235727574505356992013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3551391043178895231659221 83235727574505356992013)
                    ·
                      rfl

theorem cell23_486303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 7].length) (baseStart_486303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486303 prefixEnd_486303 := by exact prefixLift 486303
  have htrace : WordTrace (prefixWord ++ tailWord_486303) baseStart_486303 baseEnd_486303 := by
    simpa [prefixWord, tailWord_486303, baseEnd_486303] using wordTrace_append hprefix tailTrace_486303
  have hstable : (prefixWord ++ tailWord_486303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486303).length < 2 ^ (prefixWord ++ tailWord_486303).sum := by decide
  have hdescent : baseEnd_486303 < baseStart_486303 := by decide
  rcases family_descends (prefixWord ++ tailWord_486303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486343 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_486343 : Nat := 118140960795 + 486343 * 2 ^ 59
def prefixEnd_486343 : Nat := 4983230072969 + 3 ^ 40 * 486343 * 2
def baseEnd_486343 : Nat := 249727721949695914475855

theorem tailTrace_486343 : CollatzResearch.WordTrace tailWord_486343 prefixEnd_486343 249727721949695914475855 := by
  unfold tailWord_486343
  simp only [CollatzResearch.WordTrace]
  refine ⟨17738386477069846616703683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11825590984713231077802455 17738386477069846616703683)
  ·
    refine ⟨26607579715604769925055525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17738386477069846616703683 26607579715604769925055525)
    ·
      refine ⟨4988921196675894360947911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26607579715604769925055525 4988921196675894360947911)
      ·
        refine ⟨7483381795013841541421867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4988921196675894360947911 7483381795013841541421867)
        ·
          refine ⟨11225072692520762312132801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7483381795013841541421867 11225072692520762312132801)
          ·
            refine ⟨8418804519390571734099601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11225072692520762312132801 8418804519390571734099601)
            ·
              refine ⟨6314103389542928800574701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8418804519390571734099601 6314103389542928800574701)
              ·
                refine ⟨2367788771078598300215513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6314103389542928800574701 2367788771078598300215513)
                ·
                  refine ⟨1775841578308948725161635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2367788771078598300215513 1775841578308948725161635)
                  ·
                    refine ⟨2663762367463423087742453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1775841578308948725161635 2663762367463423087742453)
                    ·
                      refine ⟨249727721949695914475855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2663762367463423087742453 249727721949695914475855)
                      ·
                        rfl

theorem cell23_486343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_486343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486343 prefixEnd_486343 := by exact prefixLift 486343
  have htrace : WordTrace (prefixWord ++ tailWord_486343) baseStart_486343 baseEnd_486343 := by
    simpa [prefixWord, tailWord_486343, baseEnd_486343] using wordTrace_append hprefix tailTrace_486343
  have hstable : (prefixWord ++ tailWord_486343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486343).length < 2 ^ (prefixWord ++ tailWord_486343).sum := by decide
  have hdescent : baseEnd_486343 < baseStart_486343 := by decide
  rcases family_descends (prefixWord ++ tailWord_486343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486344 : List Nat := [2, 1, 3, 1, 5, 1, 1, 3, 1, 3, 2]
def baseStart_486344 : Nat := 118140960795 + 486344 * 2 ^ 59
def prefixEnd_486344 : Nat := 4983230072969 + 3 ^ 40 * 486344 * 2
def baseEnd_486344 : Nat := 249728235430350410563351

theorem tailTrace_486344 : CollatzResearch.WordTrace tailWord_486344 prefixEnd_486344 249728235430350410563351 := by
  unfold tailWord_486344
  simp only [CollatzResearch.WordTrace]
  refine ⟨8869211475033111893745043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11825615300044149191660057 8869211475033111893745043)
  ·
    refine ⟨13303817212549667840617565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8869211475033111893745043 13303817212549667840617565)
    ·
      refine ⟨4988931454706125440231587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13303817212549667840617565 4988931454706125440231587)
      ·
        refine ⟨7483397182059188160347381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4988931454706125440231587 7483397182059188160347381)
        ·
          refine ⟨701568485818048890032567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7483397182059188160347381 701568485818048890032567)
          ·
            refine ⟨1052352728727073335048851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701568485818048890032567 1052352728727073335048851)
            ·
              refine ⟨1578529093090610002573277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052352728727073335048851 1578529093090610002573277)
              ·
                refine ⟨591948409908978750964979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1578529093090610002573277 591948409908978750964979)
                ·
                  refine ⟨887922614863468126447469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591948409908978750964979 887922614863468126447469)
                  ·
                    refine ⟨332970980573800547417801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 887922614863468126447469 332970980573800547417801)
                    ·
                      refine ⟨249728235430350410563351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 332970980573800547417801 249728235430350410563351)
                      ·
                        rfl

theorem cell23_486344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_486344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486344 prefixEnd_486344 := by exact prefixLift 486344
  have htrace : WordTrace (prefixWord ++ tailWord_486344) baseStart_486344 baseEnd_486344 := by
    simpa [prefixWord, tailWord_486344, baseEnd_486344] using wordTrace_append hprefix tailTrace_486344
  have hstable : (prefixWord ++ tailWord_486344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486344).length < 2 ^ (prefixWord ++ tailWord_486344).sum := by decide
  have hdescent : baseEnd_486344 < baseStart_486344 := by decide
  rcases family_descends (prefixWord ++ tailWord_486344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486353 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_486353 : Nat := 118140960795 + 486353 * 2 ^ 59
def prefixEnd_486353 : Nat := 4983230072969 + 3 ^ 40 * 486353 * 2
def baseEnd_486353 : Nat := 249732856756240875350809

theorem tailTrace_486353 : CollatzResearch.WordTrace tailWord_486353 prefixEnd_486353 249732856756240875350809 := by
  unfold tailWord_486353
  simp only [CollatzResearch.WordTrace]
  refine ⟨17738751207033618324567713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11825834138022412216378475 17738751207033618324567713)
  ·
    refine ⟨13304063405275213743425785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17738751207033618324567713 13304063405275213743425785)
    ·
      refine ⟨9978047553956410307569339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13304063405275213743425785 9978047553956410307569339)
      ·
        refine ⟨14967071330934615461354009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9978047553956410307569339 14967071330934615461354009)
        ·
          refine ⟨11225303498200961596015507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14967071330934615461354009 11225303498200961596015507)
          ·
            refine ⟨16837955247301442394023261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11225303498200961596015507 16837955247301442394023261)
            ·
              refine ⟨6314233217738040897758723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16837955247301442394023261 6314233217738040897758723)
              ·
                refine ⟨9471349826607061346638085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6314233217738040897758723 9471349826607061346638085)
                ·
                  refine ⟨1775878092488824002494641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9471349826607061346638085 1775878092488824002494641)
                  ·
                    refine ⟨1331908569366618001870981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1775878092488824002494641 1331908569366618001870981)
                    ·
                      refine ⟨249732856756240875350809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1331908569366618001870981 249732856756240875350809)
                      ·
                        rfl

theorem cell23_486353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_486353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486353 prefixEnd_486353 := by exact prefixLift 486353
  have htrace : WordTrace (prefixWord ++ tailWord_486353) baseStart_486353 baseEnd_486353 := by
    simpa [prefixWord, tailWord_486353, baseEnd_486353] using wordTrace_append hprefix tailTrace_486353
  have hstable : (prefixWord ++ tailWord_486353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486353).length < 2 ^ (prefixWord ++ tailWord_486353).sum := by decide
  have hdescent : baseEnd_486353 < baseStart_486353 := by decide
  rcases family_descends (prefixWord ++ tailWord_486353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486393 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 1, 7]
def baseStart_486393 : Nat := 118140960795 + 486393 * 2 ^ 59
def prefixEnd_486393 : Nat := 4983230072969 + 3 ^ 40 * 486393 * 2
def baseEnd_486393 : Nat := 83251131994140239616875

theorem tailTrace_486393 : CollatzResearch.WordTrace tailWord_486393 prefixEnd_486393 83251131994140239616875 := by
  unfold tailWord_486393
  simp only [CollatzResearch.WordTrace]
  refine ⟨17740210126888705156023833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11826806751259136770682555 17740210126888705156023833)
  ·
    refine ⟨13305157595166528867017875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17740210126888705156023833 13305157595166528867017875)
    ·
      refine ⟨19957736392749793300526813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13305157595166528867017875 19957736392749793300526813)
      ·
        refine ⟨7484151147281172487697555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19957736392749793300526813 7484151147281172487697555)
        ·
          refine ⟨11226226720921758731546333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7484151147281172487697555 11226226720921758731546333)
          ·
            refine ⟨4209835020345659524329875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11226226720921758731546333 4209835020345659524329875)
            ·
              refine ⟨6314752530518489286494813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4209835020345659524329875 6314752530518489286494813)
              ·
                refine ⟨2368032198944433482435555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6314752530518489286494813 2368032198944433482435555)
                ·
                  refine ⟨3552048298416650223653333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368032198944433482435555 3552048298416650223653333)
                  ·
                    refine ⟨83251131994140239616875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3552048298416650223653333 83251131994140239616875)
                    ·
                      rfl

theorem cell23_486393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 7].length) (baseStart_486393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486393 prefixEnd_486393 := by exact prefixLift 486393
  have htrace : WordTrace (prefixWord ++ tailWord_486393) baseStart_486393 baseEnd_486393 := by
    simpa [prefixWord, tailWord_486393, baseEnd_486393] using wordTrace_append hprefix tailTrace_486393
  have hstable : (prefixWord ++ tailWord_486393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486393).length < 2 ^ (prefixWord ++ tailWord_486393).sum := by decide
  have hdescent : baseEnd_486393 < baseStart_486393 := by decide
  rcases family_descends (prefixWord ++ tailWord_486393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486410 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 4, 5]
def baseStart_486410 : Nat := 118140960795 + 486410 * 2 ^ 59
def prefixEnd_486410 : Nat := 4983230072969 + 3 ^ 40 * 486410 * 2
def baseEnd_486410 : Nat := 83254041717849050779349

theorem tailTrace_486410 : CollatzResearch.WordTrace tailWord_486410 prefixEnd_486410 83254041717849050779349 := by
  unfold tailWord_486410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4435207541956779264848171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11827220111884744706261789 4435207541956779264848171)
  ·
    refine ⟨6652811312935168897272257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4435207541956779264848171 6652811312935168897272257)
    ·
      refine ⟨4989608484701376672954193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6652811312935168897272257 4989608484701376672954193)
      ·
        refine ⟨3742206363526032504715645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4989608484701376672954193 3742206363526032504715645)
        ·
          refine ⟨1403327386322262189268367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3742206363526032504715645 1403327386322262189268367)
          ·
            refine ⟨2104991079483393283902551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403327386322262189268367 2104991079483393283902551)
            ·
              refine ⟨3157486619225089925853827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2104991079483393283902551 3157486619225089925853827)
              ·
                refine ⟨4736229928837634888780741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3157486619225089925853827 4736229928837634888780741)
                ·
                  refine ⟨888043111657056541646389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4736229928837634888780741 888043111657056541646389)
                  ·
                    refine ⟨83254041717849050779349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 888043111657056541646389 83254041717849050779349)
                    ·
                      rfl

theorem cell23_486410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_486410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486410 prefixEnd_486410 := by exact prefixLift 486410
  have htrace : WordTrace (prefixWord ++ tailWord_486410) baseStart_486410 baseEnd_486410 := by
    simpa [prefixWord, tailWord_486410, baseEnd_486410] using wordTrace_append hprefix tailTrace_486410
  have hstable : (prefixWord ++ tailWord_486410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486410).length < 2 ^ (prefixWord ++ tailWord_486410).sum := by decide
  have hdescent : baseEnd_486410 < baseStart_486410 := by decide
  rcases family_descends (prefixWord ++ tailWord_486410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486414 : List Nat := [4, 1, 1, 2, 2, 3, 3, 2, 5]
def baseStart_486414 : Nat := 118140960795 + 486414 * 2 ^ 59
def prefixEnd_486414 : Nat := 4983230072969 + 3 ^ 40 * 486414 * 2
def baseEnd_486414 : Nat := 27751575452907237409781

theorem tailTrace_486414 : CollatzResearch.WordTrace tailWord_486414 prefixEnd_486414 27751575452907237409781 := by
  unfold tailWord_486414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2217622007476578217817287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11827317373208417161692197 2217622007476578217817287)
  ·
    refine ⟨3326433011214867326725931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2217622007476578217817287 3326433011214867326725931)
    ·
      refine ⟨4989649516822300990088897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3326433011214867326725931 4989649516822300990088897)
      ·
        refine ⟨3742237137616725742566673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4989649516822300990088897 3742237137616725742566673)
        ·
          refine ⟨2806677853212544306925005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3742237137616725742566673 2806677853212544306925005)
          ·
            refine ⟨1052504194954704115096877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2806677853212544306925005 1052504194954704115096877)
            ·
              refine ⟨394689073108014043161329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1052504194954704115096877 394689073108014043161329)
              ·
                refine ⟨296016804831010532370997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394689073108014043161329 296016804831010532370997)
                ·
                  refine ⟨27751575452907237409781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 296016804831010532370997 27751575452907237409781)
                  ·
                    rfl

theorem cell23_486414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_486414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486414 prefixEnd_486414 := by exact prefixLift 486414
  have htrace : WordTrace (prefixWord ++ tailWord_486414) baseStart_486414 baseEnd_486414 := by
    simpa [prefixWord, tailWord_486414, baseEnd_486414] using wordTrace_append hprefix tailTrace_486414
  have hstable : (prefixWord ++ tailWord_486414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486414).length < 2 ^ (prefixWord ++ tailWord_486414).sum := by decide
  have hdescent : baseEnd_486414 < baseStart_486414 := by decide
  rcases family_descends (prefixWord ++ tailWord_486414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486483 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 2, 9]
def baseStart_486483 : Nat := 118140960795 + 486483 * 2 ^ 59
def prefixEnd_486483 : Nat := 4983230072969 + 3 ^ 40 * 486483 * 2
def baseEnd_486483 : Nat := 83266536413775122241737

theorem tailTrace_486483 : CollatzResearch.WordTrace tailWord_486483 prefixEnd_486483 83266536413775122241737 := by
  unfold tailWord_486483
  simp only [CollatzResearch.WordTrace]
  refine ⟨17743492696562650526800103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11828995131041767017866735 17743492696562650526800103)
  ·
    refine ⟨26615239044843975790200155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17743492696562650526800103 26615239044843975790200155)
    ·
      refine ⟨39922858567265963685300233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26615239044843975790200155 39922858567265963685300233)
      ·
        refine ⟨29942143925449472763975175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39922858567265963685300233 29942143925449472763975175)
        ·
          refine ⟨44913215888174209145962763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29942143925449472763975175 44913215888174209145962763)
          ·
            refine ⟨67369823832261313718944145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44913215888174209145962763 67369823832261313718944145)
            ·
              refine ⟨50527367874195985289208109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67369823832261313718944145 50527367874195985289208109)
              ·
                refine ⟨18947762952823494483453041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50527367874195985289208109 18947762952823494483453041)
                ·
                  refine ⟨14210822214617620862589781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18947762952823494483453041 14210822214617620862589781)
                  ·
                    refine ⟨83266536413775122241737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 14210822214617620862589781 83266536413775122241737)
                    ·
                      rfl

theorem cell23_486483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 9].length) (baseStart_486483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486483 prefixEnd_486483 := by exact prefixLift 486483
  have htrace : WordTrace (prefixWord ++ tailWord_486483) baseStart_486483 baseEnd_486483 := by
    simpa [prefixWord, tailWord_486483, baseEnd_486483] using wordTrace_append hprefix tailTrace_486483
  have hstable : (prefixWord ++ tailWord_486483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486483).length < 2 ^ (prefixWord ++ tailWord_486483).sum := by decide
  have hdescent : baseEnd_486483 < baseStart_486483 := by decide
  rcases family_descends (prefixWord ++ tailWord_486483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486497 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 5, 1, 3]
def baseStart_486497 : Nat := 118140960795 + 486497 * 2 ^ 59
def prefixEnd_486497 : Nat := 4983230072969 + 3 ^ 40 * 486497 * 2
def baseEnd_486497 : Nat := 249806797970488311950147

theorem tailTrace_486497 : CollatzResearch.WordTrace tailWord_486497 prefixEnd_486497 249806797970488311950147 := by
  unfold tailWord_486497
  simp only [CollatzResearch.WordTrace]
  refine ⟨17744003318511930917809745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11829335545674620611873163 17744003318511930917809745)
  ·
    refine ⟨13308002488883948188357309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17744003318511930917809745 13308002488883948188357309)
    ·
      refine ⟨4990500933331480570633991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13308002488883948188357309 4990500933331480570633991)
      ·
        refine ⟨7485751399997220855950987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4990500933331480570633991 7485751399997220855950987)
        ·
          refine ⟨11228627099995831283926481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7485751399997220855950987 11228627099995831283926481)
          ·
            refine ⟨8421470324996873462944861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11228627099995831283926481 8421470324996873462944861)
            ·
              refine ⟨3158051371873827548604323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8421470324996873462944861 3158051371873827548604323)
              ·
                refine ⟨4737077057810741322906485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158051371873827548604323 4737077057810741322906485)
                ·
                  refine ⟨444100974169756999022483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4737077057810741322906485 444100974169756999022483)
                  ·
                    refine ⟨666151461254635498533725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 444100974169756999022483 666151461254635498533725)
                    ·
                      refine ⟨249806797970488311950147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 666151461254635498533725 249806797970488311950147)
                      ·
                        rfl

theorem cell23_486497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_486497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486497 prefixEnd_486497 := by exact prefixLift 486497
  have htrace : WordTrace (prefixWord ++ tailWord_486497) baseStart_486497 baseEnd_486497 := by
    simpa [prefixWord, tailWord_486497, baseEnd_486497] using wordTrace_append hprefix tailTrace_486497
  have hstable : (prefixWord ++ tailWord_486497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486497).length < 2 ^ (prefixWord ++ tailWord_486497).sum := by decide
  have hdescent : baseEnd_486497 < baseStart_486497 := by decide
  rcases family_descends (prefixWord ++ tailWord_486497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486547 : List Nat := [1, 1, 1, 2, 1, 2, 4, 5, 2, 4]
def baseStart_486547 : Nat := 118140960795 + 486547 * 2 ^ 59
def prefixEnd_486547 : Nat := 4983230072969 + 3 ^ 40 * 486547 * 2
def baseEnd_486547 : Nat := 83277490667737705441639

theorem tailTrace_486547 : CollatzResearch.WordTrace tailWord_486547 prefixEnd_486547 83277490667737705441639 := by
  unfold tailWord_486547
  simp only [CollatzResearch.WordTrace]
  refine ⟨17745826968330789457129895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11830551312220526304753263 17745826968330789457129895)
  ·
    refine ⟨26618740452496184185694843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17745826968330789457129895 26618740452496184185694843)
    ·
      refine ⟨39928110678744276278542265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26618740452496184185694843 39928110678744276278542265)
      ·
        refine ⟨29946083009058207208906699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39928110678744276278542265 29946083009058207208906699)
        ·
          refine ⟨44919124513587310813360049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29946083009058207208906699 44919124513587310813360049)
          ·
            refine ⟨33689343385190483110020037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44919124513587310813360049 33689343385190483110020037)
            ·
              refine ⟨6316751884723215583128757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33689343385190483110020037 6316751884723215583128757)
              ·
                refine ⟨592195489192801460918321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6316751884723215583128757 592195489192801460918321)
                ·
                  refine ⟨444146616894601095688741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592195489192801460918321 444146616894601095688741)
                  ·
                    refine ⟨83277490667737705441639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 444146616894601095688741 83277490667737705441639)
                    ·
                      rfl

theorem cell23_486547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 4].length) (baseStart_486547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486547 prefixEnd_486547 := by exact prefixLift 486547
  have htrace : WordTrace (prefixWord ++ tailWord_486547) baseStart_486547 baseEnd_486547 := by
    simpa [prefixWord, tailWord_486547, baseEnd_486547] using wordTrace_append hprefix tailTrace_486547
  have hstable : (prefixWord ++ tailWord_486547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486547).length < 2 ^ (prefixWord ++ tailWord_486547).sum := by decide
  have hdescent : baseEnd_486547 < baseStart_486547 := by decide
  rcases family_descends (prefixWord ++ tailWord_486547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486554 : List Nat := [3, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4]
def baseStart_486554 : Nat := 118140960795 + 486554 * 2 ^ 59
def prefixEnd_486554 : Nat := 4983230072969 + 3 ^ 40 * 486554 * 2
def baseEnd_486554 : Nat := 249836066367794588937385

theorem tailTrace_486554 : CollatzResearch.WordTrace tailWord_486554 prefixEnd_486554 249836066367794588937385 := by
  unfold tailWord_486554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4436520569826357413158679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11830721519536953101756477 4436520569826357413158679)
  ·
    refine ⟨6654780854739536119738019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4436520569826357413158679 6654780854739536119738019)
    ·
      refine ⟨9982171282109304179607029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6654780854739536119738019 9982171282109304179607029)
      ·
        refine ⟨935828557697747266838159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9982171282109304179607029 935828557697747266838159)
        ·
          refine ⟨1403742836546620900257239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935828557697747266838159 1403742836546620900257239)
          ·
            refine ⟨2105614254819931350385859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403742836546620900257239 2105614254819931350385859)
            ·
              refine ⟨3158421382229897025578789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2105614254819931350385859 3158421382229897025578789)
              ·
                refine ⟨592204009168105692296023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3158421382229897025578789 592204009168105692296023)
                ·
                  refine ⟨888306013752158538444035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592204009168105692296023 888306013752158538444035)
                  ·
                    refine ⟨1332459020628237807666053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 888306013752158538444035 1332459020628237807666053)
                    ·
                      refine ⟨249836066367794588937385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1332459020628237807666053 249836066367794588937385)
                      ·
                        rfl

theorem cell23_486554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_486554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486554 prefixEnd_486554 := by exact prefixLift 486554
  have htrace : WordTrace (prefixWord ++ tailWord_486554) baseStart_486554 baseEnd_486554 := by
    simpa [prefixWord, tailWord_486554, baseEnd_486554] using wordTrace_append hprefix tailTrace_486554
  have hstable : (prefixWord ++ tailWord_486554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486554).length < 2 ^ (prefixWord ++ tailWord_486554).sum := by decide
  have hdescent : baseEnd_486554 < baseStart_486554 := by decide
  rcases family_descends (prefixWord ++ tailWord_486554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486560 : List Nat := [2, 1, 1, 4, 2, 1, 3, 9]
def baseStart_486560 : Nat := 118140960795 + 486560 * 2 ^ 59
def prefixEnd_486560 : Nat := 4983230072969 + 3 ^ 40 * 486560 * 2
def baseEnd_486560 : Nat := 9253301750063761683791

theorem tailTrace_486560 : CollatzResearch.WordTrace tailWord_486560 prefixEnd_486560 9253301750063761683791 := by
  unfold tailWord_486560
  simp only [CollatzResearch.WordTrace]
  refine ⟨8873150558641846338676567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11830867411522461784902089 8873150558641846338676567)
  ·
    refine ⟨13309725837962769508014851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8873150558641846338676567 13309725837962769508014851)
    ·
      refine ⟨19964588756944154262022277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13309725837962769508014851 19964588756944154262022277)
      ·
        refine ⟨3743360391927028924129177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19964588756944154262022277 3743360391927028924129177)
        ·
          refine ⟨2807520293945271693096883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3743360391927028924129177 2807520293945271693096883)
          ·
            refine ⟨4211280440917907539645325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807520293945271693096883 4211280440917907539645325)
            ·
              refine ⟨1579230165344215327366997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4211280440917907539645325 1579230165344215327366997)
              ·
                refine ⟨9253301750063761683791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1579230165344215327366997 9253301750063761683791)
                ·
                  rfl

theorem cell23_486560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 9].length) (baseStart_486560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486560 prefixEnd_486560 := by exact prefixLift 486560
  have htrace : WordTrace (prefixWord ++ tailWord_486560) baseStart_486560 baseEnd_486560 := by
    simpa [prefixWord, tailWord_486560, baseEnd_486560] using wordTrace_append hprefix tailTrace_486560
  have hstable : (prefixWord ++ tailWord_486560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486560).length < 2 ^ (prefixWord ++ tailWord_486560).sum := by decide
  have hdescent : baseEnd_486560 < baseStart_486560 := by decide
  rcases family_descends (prefixWord ++ tailWord_486560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486577 : List Nat := [1, 2, 2, 5, 1, 3, 9]
def baseStart_486577 : Nat := 118140960795 + 486577 * 2 ^ 59
def prefixEnd_486577 : Nat := 4983230072969 + 3 ^ 40 * 486577 * 2
def baseEnd_486577 : Nat := 3084541684232691345059

theorem tailTrace_486577 : CollatzResearch.WordTrace tailWord_486577 prefixEnd_486577 3084541684232691345059 := by
  unfold tailWord_486577
  simp only [CollatzResearch.WordTrace]
  refine ⟨17746921158222104580721985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11831280772148069720481323 17746921158222104580721985)
  ·
    refine ⟨13310190868666578435541489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17746921158222104580721985 13310190868666578435541489)
    ·
      refine ⟨9982643151499933826656117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13310190868666578435541489 9982643151499933826656117)
      ·
        refine ⟨935872795453118796249011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9982643151499933826656117 935872795453118796249011)
        ·
          refine ⟨1403809193179678194373517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935872795453118796249011 1403809193179678194373517)
          ·
            refine ⟨526428447442379322890069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1403809193179678194373517 526428447442379322890069)
            ·
              refine ⟨3084541684232691345059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 526428447442379322890069 3084541684232691345059)
              ·
                rfl

theorem cell23_486577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 9].length) (baseStart_486577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486577 prefixEnd_486577 := by exact prefixLift 486577
  have htrace : WordTrace (prefixWord ++ tailWord_486577) baseStart_486577 baseEnd_486577 := by
    simpa [prefixWord, tailWord_486577, baseEnd_486577] using wordTrace_append hprefix tailTrace_486577
  have hstable : (prefixWord ++ tailWord_486577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486577).length < 2 ^ (prefixWord ++ tailWord_486577).sum := by decide
  have hdescent : baseEnd_486577 < baseStart_486577 := by decide
  rcases family_descends (prefixWord ++ tailWord_486577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486582 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_486582 : Nat := 118140960795 + 486582 * 2 ^ 59
def prefixEnd_486582 : Nat := 4983230072969 + 3 ^ 40 * 486582 * 2
def baseEnd_486582 : Nat := 249850443826120479387257

theorem tailTrace_486582 : CollatzResearch.WordTrace tailWord_486582 prefixEnd_486582 249850443826120479387257 := by
  unfold tailWord_486582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1109193970200249402165875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11831402348802660289769333 1109193970200249402165875)
  ·
    refine ⟨1663790955300374103248813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1109193970200249402165875 1663790955300374103248813)
    ·
      refine ⟨623921608237640288718305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1663790955300374103248813 623921608237640288718305)
      ·
        refine ⟨467941206178230216538729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623921608237640288718305 467941206178230216538729)
        ·
          refine ⟨350955904633672662404047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467941206178230216538729 350955904633672662404047)
          ·
            refine ⟨526433856950508993606071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350955904633672662404047 526433856950508993606071)
            ·
              refine ⟨789650785425763490409107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526433856950508993606071 789650785425763490409107)
              ·
                refine ⟨1184476178138645235613661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789650785425763490409107 1184476178138645235613661)
                ·
                  refine ⟨444178566801991963355123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184476178138645235613661 444178566801991963355123)
                  ·
                    refine ⟨666267850202987945032685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 444178566801991963355123 666267850202987945032685)
                    ·
                      refine ⟨249850443826120479387257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 666267850202987945032685 249850443826120479387257)
                      ·
                        rfl

theorem cell23_486582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_486582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486582 prefixEnd_486582 := by exact prefixLift 486582
  have htrace : WordTrace (prefixWord ++ tailWord_486582) baseStart_486582 baseEnd_486582 := by
    simpa [prefixWord, tailWord_486582, baseEnd_486582] using wordTrace_append hprefix tailTrace_486582
  have hstable : (prefixWord ++ tailWord_486582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486582).length < 2 ^ (prefixWord ++ tailWord_486582).sum := by decide
  have hdescent : baseEnd_486582 < baseStart_486582 := by decide
  rcases family_descends (prefixWord ++ tailWord_486582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486588 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 3, 2, 2]
def baseStart_486588 : Nat := 118140960795 + 486588 * 2 ^ 59
def prefixEnd_486588 : Nat := 4983230072969 + 3 ^ 40 * 486588 * 2
def baseEnd_486588 : Nat := 249853524710047455912229

theorem tailTrace_486588 : CollatzResearch.WordTrace tailWord_486588 prefixEnd_486588 249853524710047455912229 := by
  unfold tailWord_486588
  simp only [CollatzResearch.WordTrace]
  refine ⟨8873661180591126729686209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11831548240788168972914945 8873661180591126729686209)
  ·
    refine ⟨6655245885443345047264657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8873661180591126729686209 6655245885443345047264657)
    ·
      refine ⟨4991434414082508785448493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6655245885443345047264657 4991434414082508785448493)
      ·
        refine ⟨1871787905280940794543185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4991434414082508785448493 1871787905280940794543185)
        ·
          refine ⟨1403840928960705595907389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1871787905280940794543185 1403840928960705595907389)
          ·
            refine ⟨526440348360264598465271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1403840928960705595907389 526440348360264598465271)
            ·
              refine ⟨789660522540396897697907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526440348360264598465271 789660522540396897697907)
              ·
                refine ⟨1184490783810595346546861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789660522540396897697907 1184490783810595346546861)
                ·
                  refine ⟨444184043928973254955073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184490783810595346546861 444184043928973254955073)
                  ·
                    refine ⟨333138032946729941216305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 444184043928973254955073 333138032946729941216305)
                    ·
                      refine ⟨249853524710047455912229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 333138032946729941216305 249853524710047455912229)
                      ·
                        rfl

theorem cell23_486588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_486588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486588 prefixEnd_486588 := by exact prefixLift 486588
  have htrace : WordTrace (prefixWord ++ tailWord_486588) baseStart_486588 baseEnd_486588 := by
    simpa [prefixWord, tailWord_486588, baseEnd_486588] using wordTrace_append hprefix tailTrace_486588
  have hstable : (prefixWord ++ tailWord_486588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486588).length < 2 ^ (prefixWord ++ tailWord_486588).sum := by decide
  have hdescent : baseEnd_486588 < baseStart_486588 := by decide
  rcases family_descends (prefixWord ++ tailWord_486588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486597 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 2, 7, 2]
def baseStart_486597 : Nat := 118140960795 + 486597 * 2 ^ 59
def prefixEnd_486597 : Nat := 4983230072969 + 3 ^ 40 * 486597 * 2
def baseEnd_486597 : Nat := 249858146035937920699687

theorem tailTrace_486597 : CollatzResearch.WordTrace tailWord_486597 prefixEnd_486597 249858146035937920699687 := by
  unfold tailWord_486597
  simp only [CollatzResearch.WordTrace]
  refine ⟨17747650618149647996450045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11831767078766431997633363 17747650618149647996450045)
  ·
    refine ⟨6655368981806117998668767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17747650618149647996450045 6655368981806117998668767)
    ·
      refine ⟨9983053472709176998003151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6655368981806117998668767 9983053472709176998003151)
      ·
        refine ⟨14974580209063765497004727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9983053472709176998003151 14974580209063765497004727)
        ·
          refine ⟨22461870313595648245507091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14974580209063765497004727 22461870313595648245507091)
          ·
            refine ⟨33692805470393472368260637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22461870313595648245507091 33692805470393472368260637)
            ·
              refine ⟨12634802051397552138097739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33692805470393472368260637 12634802051397552138097739)
              ·
                refine ⟨18952203077096328207146609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12634802051397552138097739 18952203077096328207146609)
                ·
                  refine ⟨14214152307822246155359957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18952203077096328207146609 14214152307822246155359957)
                  ·
                    refine ⟨333144194714583894266249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14214152307822246155359957 333144194714583894266249)
                    ·
                      refine ⟨249858146035937920699687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 333144194714583894266249 249858146035937920699687)
                      ·
                        rfl

theorem cell23_486597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 7, 2].length) (baseStart_486597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486597 prefixEnd_486597 := by exact prefixLift 486597
  have htrace : WordTrace (prefixWord ++ tailWord_486597) baseStart_486597 baseEnd_486597 := by
    simpa [prefixWord, tailWord_486597, baseEnd_486597] using wordTrace_append hprefix tailTrace_486597
  have hstable : (prefixWord ++ tailWord_486597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486597).length < 2 ^ (prefixWord ++ tailWord_486597).sum := by decide
  have hdescent : baseEnd_486597 < baseStart_486597 := by decide
  rcases family_descends (prefixWord ++ tailWord_486597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486605 : List Nat := [1, 6, 2, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_486605 : Nat := 118140960795 + 486605 * 2 ^ 59
def prefixEnd_486605 : Nat := 4983230072969 + 3 ^ 40 * 486605 * 2
def baseEnd_486605 : Nat := 249862253881173889399651

theorem tailTrace_486605 : CollatzResearch.WordTrace tailWord_486605 prefixEnd_486605 249862253881173889399651 := by
  unfold tailWord_486605
  simp only [CollatzResearch.WordTrace]
  refine ⟨17747942402120665362741269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11831961601413776908494179 17747942402120665362741269)
  ·
    refine ⟨831934800099406188878497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17747942402120665362741269 831934800099406188878497)
    ·
      refine ⟨623951100074554641658873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 831934800099406188878497 623951100074554641658873)
      ·
        refine ⟨467963325055915981244155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623951100074554641658873 467963325055915981244155)
        ·
          refine ⟨701944987583873971866233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467963325055915981244155 701944987583873971866233)
          ·
            refine ⟨526458740687905478899675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701944987583873971866233 526458740687905478899675)
            ·
              refine ⟨789688111031858218349513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526458740687905478899675 789688111031858218349513)
              ·
                refine ⟨592266083273893663762135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 789688111031858218349513 592266083273893663762135)
                ·
                  refine ⟨888399124910840495643203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592266083273893663762135 888399124910840495643203)
                  ·
                    refine ⟨1332598687366260743464805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 888399124910840495643203 1332598687366260743464805)
                    ·
                      refine ⟨249862253881173889399651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1332598687366260743464805 249862253881173889399651)
                      ·
                        rfl

theorem cell23_486605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_486605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486605 prefixEnd_486605 := by exact prefixLift 486605
  have htrace : WordTrace (prefixWord ++ tailWord_486605) baseStart_486605 baseEnd_486605 := by
    simpa [prefixWord, tailWord_486605, baseEnd_486605] using wordTrace_append hprefix tailTrace_486605
  have hstable : (prefixWord ++ tailWord_486605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486605).length < 2 ^ (prefixWord ++ tailWord_486605).sum := by decide
  have hdescent : baseEnd_486605 < baseStart_486605 := by decide
  rcases family_descends (prefixWord ++ tailWord_486605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486621 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_486621 : Nat := 118140960795 + 486621 * 2 ^ 59
def prefixEnd_486621 : Nat := 4983230072969 + 3 ^ 40 * 486621 * 2
def baseEnd_486621 : Nat := 249870469571645826799577

theorem tailTrace_486621 : CollatzResearch.WordTrace tailWord_486621 prefixEnd_486621 249870469571645826799577 := by
  unfold tailWord_486621
  simp only [CollatzResearch.WordTrace]
  refine ⟨17748525970062700095323717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11832350646708466730215811 17748525970062700095323717)
  ·
    refine ⟨3327848619386756267873197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17748525970062700095323717 3327848619386756267873197)
    ·
      refine ⟨1247943232270033600452449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3327848619386756267873197 1247943232270033600452449)
      ·
        refine ⟨935957424202525200339337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1247943232270033600452449 935957424202525200339337)
        ·
          refine ⟨701968068151893900254503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 935957424202525200339337 701968068151893900254503)
          ·
            refine ⟨1052952102227840850381755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701968068151893900254503 1052952102227840850381755)
            ·
              refine ⟨1579428153341761275572633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052952102227840850381755 1579428153341761275572633)
              ·
                refine ⟨1184571115006320956679475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579428153341761275572633 1184571115006320956679475)
                ·
                  refine ⟨1776856672509481435019213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184571115006320956679475 1776856672509481435019213)
                  ·
                    refine ⟨666321252191055538132205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1776856672509481435019213 666321252191055538132205)
                    ·
                      refine ⟨249870469571645826799577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 666321252191055538132205 249870469571645826799577)
                      ·
                        rfl

theorem cell23_486621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_486621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486621 prefixEnd_486621 := by exact prefixLift 486621
  have htrace : WordTrace (prefixWord ++ tailWord_486621) baseStart_486621 baseEnd_486621 := by
    simpa [prefixWord, tailWord_486621, baseEnd_486621] using wordTrace_append hprefix tailTrace_486621
  have hstable : (prefixWord ++ tailWord_486621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486621).length < 2 ^ (prefixWord ++ tailWord_486621).sum := by decide
  have hdescent : baseEnd_486621 < baseStart_486621 := by decide
  rcases family_descends (prefixWord ++ tailWord_486621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486640 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 6]
def baseStart_486640 : Nat := 118140960795 + 486640 * 2 ^ 59
def prefixEnd_486640 : Nat := 4983230072969 + 3 ^ 40 * 486640 * 2
def baseEnd_486640 : Nat := 249880225704081252461989

theorem tailTrace_486640 : CollatzResearch.WordTrace tailWord_486640 prefixEnd_486640 249880225704081252461989 := by
  unfold tailWord_486640
  simp only [CollatzResearch.WordTrace]
  refine ⟨8874609478496933170132687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11832812637995910893510249 8874609478496933170132687)
  ·
    refine ⟨13311914217745399755199031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8874609478496933170132687 13311914217745399755199031)
    ·
      refine ⟨19967871326618099632798547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13311914217745399755199031 19967871326618099632798547)
      ·
        refine ⟨29951806989927149449197821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19967871326618099632798547 29951806989927149449197821)
        ·
          refine ⟨11231927621222681043449183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29951806989927149449197821 11231927621222681043449183)
          ·
            refine ⟨16847891431834021565173775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11231927621222681043449183 16847891431834021565173775)
            ·
              refine ⟨25271837147751032347760663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16847891431834021565173775 25271837147751032347760663)
              ·
                refine ⟨37907755721626548521640995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25271837147751032347760663 37907755721626548521640995)
                ·
                  refine ⟨56861633582439822782461493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37907755721626548521640995 56861633582439822782461493)
                  ·
                    refine ⟨5330778148353733385855765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56861633582439822782461493 5330778148353733385855765)
                    ·
                      refine ⟨249880225704081252461989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5330778148353733385855765 249880225704081252461989)
                      ·
                        rfl

theorem cell23_486640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_486640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486640 prefixEnd_486640 := by exact prefixLift 486640
  have htrace : WordTrace (prefixWord ++ tailWord_486640) baseStart_486640 baseEnd_486640 := by
    simpa [prefixWord, tailWord_486640, baseEnd_486640] using wordTrace_append hprefix tailTrace_486640
  have hstable : (prefixWord ++ tailWord_486640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486640).length < 2 ^ (prefixWord ++ tailWord_486640).sum := by decide
  have hdescent : baseEnd_486640 < baseStart_486640 := by decide
  rcases family_descends (prefixWord ++ tailWord_486640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486654 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_486654 : Nat := 118140960795 + 486654 * 2 ^ 59
def prefixEnd_486654 : Nat := 4983230072969 + 3 ^ 40 * 486654 * 2
def baseEnd_486654 : Nat := 83295804811081399228975

theorem tailTrace_486654 : CollatzResearch.WordTrace tailWord_486654 prefixEnd_486654 83295804811081399228975 := by
  unfold tailWord_486654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2218716197367893341409377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11833153052628764487516677 2218716197367893341409377)
  ·
    refine ⟨1664037148025920006057033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2218716197367893341409377 1664037148025920006057033)
    ·
      refine ⟨1248027861019440004542775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1664037148025920006057033 1248027861019440004542775)
      ·
        refine ⟨1872041791529160006814163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1248027861019440004542775 1872041791529160006814163)
        ·
          refine ⟨2808062687293740010221245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1872041791529160006814163 2808062687293740010221245)
          ·
            refine ⟨1053023507735152503832967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2808062687293740010221245 1053023507735152503832967)
            ·
              refine ⟨1579535261602728755749451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053023507735152503832967 1579535261602728755749451)
              ·
                refine ⟨2369302892404093133624177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579535261602728755749451 2369302892404093133624177)
                ·
                  refine ⟨1776977169303069850218133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2369302892404093133624177 1776977169303069850218133)
                  ·
                    refine ⟨83295804811081399228975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1776977169303069850218133 83295804811081399228975)
                    ·
                      rfl

theorem cell23_486654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_486654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486654 prefixEnd_486654 := by exact prefixLift 486654
  have htrace : WordTrace (prefixWord ++ tailWord_486654) baseStart_486654 baseEnd_486654 := by
    simpa [prefixWord, tailWord_486654, baseEnd_486654] using wordTrace_append hprefix tailTrace_486654
  have hstable : (prefixWord ++ tailWord_486654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486654).length < 2 ^ (prefixWord ++ tailWord_486654).sum := by decide
  have hdescent : baseEnd_486654 < baseStart_486654 := by decide
  rcases family_descends (prefixWord ++ tailWord_486654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486657 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_486657 : Nat := 118140960795 + 486657 * 2 ^ 59
def prefixEnd_486657 : Nat := 4983230072969 + 3 ^ 40 * 486657 * 2
def baseEnd_486657 : Nat := 249888954875207685949411

theorem tailTrace_486657 : CollatzResearch.WordTrace tailWord_486657 prefixEnd_486657 249888954875207685949411 := by
  unfold tailWord_486657
  simp only [CollatzResearch.WordTrace]
  refine ⟨17749838997932278243634225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11833225998621518829089483 17749838997932278243634225)
  ·
    refine ⟨13312379248449208682725669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17749838997932278243634225 13312379248449208682725669)
    ·
      refine ⟨2496071109084226628011063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13312379248449208682725669 2496071109084226628011063)
      ·
        refine ⟨3744106663626339942016595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496071109084226628011063 3744106663626339942016595)
        ·
          refine ⟨5616159995439509913024893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3744106663626339942016595 5616159995439509913024893)
          ·
            refine ⟨2106059998289816217384335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5616159995439509913024893 2106059998289816217384335)
            ·
              refine ⟨3159089997434724326076503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2106059998289816217384335 3159089997434724326076503)
              ·
                refine ⟨4738634996152086489114755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3159089997434724326076503 4738634996152086489114755)
                ·
                  refine ⟨7107952494228129733672133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738634996152086489114755 7107952494228129733672133)
                  ·
                    refine ⟨1332741092667774325063525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7107952494228129733672133 1332741092667774325063525)
                    ·
                      refine ⟨249888954875207685949411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1332741092667774325063525 249888954875207685949411)
                      ·
                        rfl

theorem cell23_486657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_486657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486657 prefixEnd_486657 := by exact prefixLift 486657
  have htrace : WordTrace (prefixWord ++ tailWord_486657) baseStart_486657 baseEnd_486657 := by
    simpa [prefixWord, tailWord_486657, baseEnd_486657] using wordTrace_append hprefix tailTrace_486657
  have hstable : (prefixWord ++ tailWord_486657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486657).length < 2 ^ (prefixWord ++ tailWord_486657).sum := by decide
  have hdescent : baseEnd_486657 < baseStart_486657 := by decide
  rcases family_descends (prefixWord ++ tailWord_486657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486661 : List Nat := [1, 3, 1, 1, 2, 1, 3, 5, 2, 2, 2]
def baseStart_486661 : Nat := 118140960795 + 486661 * 2 ^ 59
def prefixEnd_486661 : Nat := 4983230072969 + 3 ^ 40 * 486661 * 2
def baseEnd_486661 : Nat := 249891008797825670299393

theorem tailTrace_486661 : CollatzResearch.WordTrace tailWord_486661 prefixEnd_486661 249891008797825670299393 := by
  unfold tailWord_486661
  simp only [CollatzResearch.WordTrace]
  refine ⟨17749984889917786926779837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11833323259945191284519891 17749984889917786926779837)
  ·
    refine ⟨6656244333719170097542439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17749984889917786926779837 6656244333719170097542439)
    ·
      refine ⟨9984366500578755146313659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6656244333719170097542439 9984366500578755146313659)
      ·
        refine ⟨14976549750868132719470489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9984366500578755146313659 14976549750868132719470489)
        ·
          refine ⟨11232412313151099539602867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14976549750868132719470489 11232412313151099539602867)
          ·
            refine ⟨16848618469726649309404301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11232412313151099539602867 16848618469726649309404301)
            ·
              refine ⟨6318231926147493491026613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16848618469726649309404301 6318231926147493491026613)
              ·
                refine ⟨592334243076327514783745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6318231926147493491026613 592334243076327514783745)
                ·
                  refine ⟨444250682307245636087809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592334243076327514783745 444250682307245636087809)
                  ·
                    refine ⟨333188011730434227065857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 444250682307245636087809 333188011730434227065857)
                    ·
                      refine ⟨249891008797825670299393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 333188011730434227065857 249891008797825670299393)
                      ·
                        rfl

theorem cell23_486661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 2, 2].length) (baseStart_486661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486661 prefixEnd_486661 := by exact prefixLift 486661
  have htrace : WordTrace (prefixWord ++ tailWord_486661) baseStart_486661 baseEnd_486661 := by
    simpa [prefixWord, tailWord_486661, baseEnd_486661] using wordTrace_append hprefix tailTrace_486661
  have hstable : (prefixWord ++ tailWord_486661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486661).length < 2 ^ (prefixWord ++ tailWord_486661).sum := by decide
  have hdescent : baseEnd_486661 < baseStart_486661 := by decide
  rcases family_descends (prefixWord ++ tailWord_486661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486667 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 7]
def baseStart_486667 : Nat := 118140960795 + 486667 * 2 ^ 59
def prefixEnd_486667 : Nat := 4983230072969 + 3 ^ 40 * 486667 * 2
def baseEnd_486667 : Nat := 27766009964639182980485

theorem tailTrace_486667 : CollatzResearch.WordTrace tailWord_486667 prefixEnd_486667 27766009964639182980485 := by
  unfold tailWord_486667
  simp only [CollatzResearch.WordTrace]
  refine ⟨17750203727896049951498255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11833469151930699967665503 17750203727896049951498255)
  ·
    refine ⟨26625305591844074927247383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17750203727896049951498255 26625305591844074927247383)
    ·
      refine ⟨39937958387766112390871075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26625305591844074927247383 39937958387766112390871075)
      ·
        refine ⟨59906937581649168586306613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39937958387766112390871075 59906937581649168586306613)
        ·
          refine ⟨5616275398279609554966245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59906937581649168586306613 5616275398279609554966245)
          ·
            refine ⟨1053051637177426791556171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5616275398279609554966245 1053051637177426791556171)
            ·
              refine ⟨1579577455766140187334257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053051637177426791556171 1579577455766140187334257)
              ·
                refine ⟨1184683091824605140500693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579577455766140187334257 1184683091824605140500693)
                ·
                  refine ⟨27766009964639182980485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1184683091824605140500693 27766009964639182980485)
                  ·
                    rfl

theorem cell23_486667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 7].length) (baseStart_486667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486667 prefixEnd_486667 := by exact prefixLift 486667
  have htrace : WordTrace (prefixWord ++ tailWord_486667) baseStart_486667 baseEnd_486667 := by
    simpa [prefixWord, tailWord_486667, baseEnd_486667] using wordTrace_append hprefix tailTrace_486667
  have hstable : (prefixWord ++ tailWord_486667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486667).length < 2 ^ (prefixWord ++ tailWord_486667).sum := by decide
  have hdescent : baseEnd_486667 < baseStart_486667 := by decide
  rcases family_descends (prefixWord ++ tailWord_486667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486677 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_486677 : Nat := 118140960795 + 486677 * 2 ^ 59
def prefixEnd_486677 : Nat := 4983230072969 + 3 ^ 40 * 486677 * 2
def baseEnd_486677 : Nat := 249899224488297607699319

theorem tailTrace_486677 : CollatzResearch.WordTrace tailWord_486677 prefixEnd_486677 249899224488297607699319 := by
  unfold tailWord_486677
  simp only [CollatzResearch.WordTrace]
  refine ⟨17750568457859821659362285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11833712305239881106241523 17750568457859821659362285)
  ·
    refine ⟨6656463171697433122260857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17750568457859821659362285 6656463171697433122260857)
    ·
      refine ⟨4992347378773074841695643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6656463171697433122260857 4992347378773074841695643)
      ·
        refine ⟨7488521068159612262543465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4992347378773074841695643 7488521068159612262543465)
        ·
          refine ⟨5616390801119709196907599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7488521068159612262543465 5616390801119709196907599)
          ·
            refine ⟨8424586201679563795361399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5616390801119709196907599 8424586201679563795361399)
            ·
              refine ⟨12636879302519345693042099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8424586201679563795361399 12636879302519345693042099)
              ·
                refine ⟨18955318953779018539563149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12636879302519345693042099 18955318953779018539563149)
                ·
                  refine ⟨7108244607667131952336181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18955318953779018539563149 7108244607667131952336181)
                  ·
                    refine ⟨666397931968793620531517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7108244607667131952336181 666397931968793620531517)
                    ·
                      refine ⟨249899224488297607699319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 666397931968793620531517 249899224488297607699319)
                      ·
                        rfl

theorem cell23_486677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_486677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486677 prefixEnd_486677 := by exact prefixLift 486677
  have htrace : WordTrace (prefixWord ++ tailWord_486677) baseStart_486677 baseEnd_486677 := by
    simpa [prefixWord, tailWord_486677, baseEnd_486677] using wordTrace_append hprefix tailTrace_486677
  have hstable : (prefixWord ++ tailWord_486677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486677).length < 2 ^ (prefixWord ++ tailWord_486677).sum := by decide
  have hdescent : baseEnd_486677 < baseStart_486677 := by decide
  rcases family_descends (prefixWord ++ tailWord_486677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486684 : List Nat := [2, 2, 3, 1, 1, 1, 3, 5, 5]
def baseStart_486684 : Nat := 118140960795 + 486684 * 2 ^ 59
def prefixEnd_486684 : Nat := 4983230072969 + 3 ^ 40 * 486684 * 2
def baseEnd_486684 : Nat := 27766979872542120034643

theorem tailTrace_486684 : CollatzResearch.WordTrace tailWord_486684 prefixEnd_486684 27766979872542120034643 := by
  unfold tailWord_486684
  simp only [CollatzResearch.WordTrace]
  refine ⟨8875411884417230927433553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11833882512556307903244737 8875411884417230927433553)
  ·
    refine ⟨6656558913312923195575165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8875411884417230927433553 6656558913312923195575165)
    ·
      refine ⟨2496209592492346198340687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6656558913312923195575165 2496209592492346198340687)
      ·
        refine ⟨3744314388738519297511031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496209592492346198340687 3744314388738519297511031)
        ·
          refine ⟨5616471583107778946266547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3744314388738519297511031 5616471583107778946266547)
          ·
            refine ⟨8424707374661668419399821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5616471583107778946266547 8424707374661668419399821)
            ·
              refine ⟨3159265265498125657274933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8424707374661668419399821 3159265265498125657274933)
              ·
                refine ⟨296181118640449280369525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3159265265498125657274933 296181118640449280369525)
                ·
                  refine ⟨27766979872542120034643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 296181118640449280369525 27766979872542120034643)
                  ·
                    rfl

theorem cell23_486684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 5].length) (baseStart_486684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486684 prefixEnd_486684 := by exact prefixLift 486684
  have htrace : WordTrace (prefixWord ++ tailWord_486684) baseStart_486684 baseEnd_486684 := by
    simpa [prefixWord, tailWord_486684, baseEnd_486684] using wordTrace_append hprefix tailTrace_486684
  have hstable : (prefixWord ++ tailWord_486684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486684).length < 2 ^ (prefixWord ++ tailWord_486684).sum := by decide
  have hdescent : baseEnd_486684 < baseStart_486684 := by decide
  rcases family_descends (prefixWord ++ tailWord_486684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486701 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 7]
def baseStart_486701 : Nat := 118140960795 + 486701 * 2 ^ 59
def prefixEnd_486701 : Nat := 4983230072969 + 3 ^ 40 * 486701 * 2
def baseEnd_486701 : Nat := 27767949780445057088801

theorem tailTrace_486701 : CollatzResearch.WordTrace tailWord_486701 prefixEnd_486701 27767949780445057088801 := by
  unfold tailWord_486701
  simp only [CollatzResearch.WordTrace]
  refine ⟨17751443809772873758235957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11834295873181915838823971 17751443809772873758235957)
  ·
    refine ⟨1664197857166206914834621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17751443809772873758235957 1664197857166206914834621)
    ·
      refine ⟨624074196437327593062983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1664197857166206914834621 624074196437327593062983)
      ·
        refine ⟨936111294655991389594475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624074196437327593062983 936111294655991389594475)
        ·
          refine ⟨1404166941983987084391713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936111294655991389594475 1404166941983987084391713)
          ·
            refine ⟨1053125206487990313293785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1404166941983987084391713 1053125206487990313293785)
            ·
              refine ⟨789843904865992734970339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053125206487990313293785 789843904865992734970339)
              ·
                refine ⟨1184765857298989102455509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789843904865992734970339 1184765857298989102455509)
                ·
                  refine ⟨27767949780445057088801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1184765857298989102455509 27767949780445057088801)
                  ·
                    rfl

theorem cell23_486701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_486701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486701 prefixEnd_486701 := by exact prefixLift 486701
  have htrace : WordTrace (prefixWord ++ tailWord_486701) baseStart_486701 baseEnd_486701 := by
    simpa [prefixWord, tailWord_486701, baseEnd_486701] using wordTrace_append hprefix tailTrace_486701
  have hstable : (prefixWord ++ tailWord_486701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486701).length < 2 ^ (prefixWord ++ tailWord_486701).sum := by decide
  have hdescent : baseEnd_486701 < baseStart_486701 := by decide
  rcases family_descends (prefixWord ++ tailWord_486701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486734 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_486734 : Nat := 118140960795 + 486734 * 2 ^ 59
def prefixEnd_486734 : Nat := 4983230072969 + 3 ^ 40 * 486734 * 2
def baseEnd_486734 : Nat := 249928492885603884686557

theorem tailTrace_486734 : CollatzResearch.WordTrace tailWord_486734 prefixEnd_486734 249928492885603884686557 := by
  unfold tailWord_486734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2219080927331665049273407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11835098279102213596124837 2219080927331665049273407)
  ·
    refine ⟨3328621390997497573910111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2219080927331665049273407 3328621390997497573910111)
    ·
      refine ⟨4992932086496246360865167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3328621390997497573910111 4992932086496246360865167)
      ·
        refine ⟨7489398129744369541297751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4992932086496246360865167 7489398129744369541297751)
        ·
          refine ⟨11234097194616554311946627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7489398129744369541297751 11234097194616554311946627)
          ·
            refine ⟨16851145791924831467919941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11234097194616554311946627 16851145791924831467919941)
            ·
              refine ⟨3159589835985905900234989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16851145791924831467919941 3159589835985905900234989)
              ·
                refine ⟨1184846188494714712588121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3159589835985905900234989 1184846188494714712588121)
                ·
                  refine ⟨888634641371036034441091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1184846188494714712588121 888634641371036034441091)
                  ·
                    refine ⟨1332951962056554051661637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 888634641371036034441091 1332951962056554051661637)
                    ·
                      refine ⟨249928492885603884686557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1332951962056554051661637 249928492885603884686557)
                      ·
                        rfl

theorem cell23_486734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_486734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486734 prefixEnd_486734 := by exact prefixLift 486734
  have htrace : WordTrace (prefixWord ++ tailWord_486734) baseStart_486734 baseEnd_486734 := by
    simpa [prefixWord, tailWord_486734, baseEnd_486734] using wordTrace_append hprefix tailTrace_486734
  have hstable : (prefixWord ++ tailWord_486734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486734).length < 2 ^ (prefixWord ++ tailWord_486734).sum := by decide
  have hdescent : baseEnd_486734 < baseStart_486734 := by decide
  rcases family_descends (prefixWord ++ tailWord_486734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486757 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 8]
def baseStart_486757 : Nat := 118140960795 + 486757 * 2 ^ 59
def prefixEnd_486757 : Nat := 4983230072969 + 3 ^ 40 * 486757 * 2
def baseEnd_486757 : Nat := 27771144771184143855439

theorem tailTrace_486757 : CollatzResearch.WordTrace tailWord_486757 prefixEnd_486757 27771144771184143855439 := by
  unfold tailWord_486757
  simp only [CollatzResearch.WordTrace]
  refine ⟨17753486297569995322274525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11835657531713330214849683 17753486297569995322274525)
  ·
    refine ⟨6657557361588748245852947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17753486297569995322274525 6657557361588748245852947)
    ·
      refine ⟨9986336042383122368779421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6657557361588748245852947 9986336042383122368779421)
      ·
        refine ⟨3744876015893670888292283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9986336042383122368779421 3744876015893670888292283)
        ·
          refine ⟨5617314023840506332438425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3744876015893670888292283 5617314023840506332438425)
          ·
            refine ⟨4212985517880379749328819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5617314023840506332438425 4212985517880379749328819)
            ·
              refine ⟨6319478276820569623993229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4212985517880379749328819 6319478276820569623993229)
              ·
                refine ⟨2369804353807713608997461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6319478276820569623993229 2369804353807713608997461)
                ·
                  refine ⟨27771144771184143855439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2369804353807713608997461 27771144771184143855439)
                  ·
                    rfl

theorem cell23_486757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_486757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486757 prefixEnd_486757 := by exact prefixLift 486757
  have htrace : WordTrace (prefixWord ++ tailWord_486757) baseStart_486757 baseEnd_486757 := by
    simpa [prefixWord, tailWord_486757, baseEnd_486757] using wordTrace_append hprefix tailTrace_486757
  have hstable : (prefixWord ++ tailWord_486757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486757).length < 2 ^ (prefixWord ++ tailWord_486757).sum := by decide
  have hdescent : baseEnd_486757 < baseStart_486757 := by decide
  rcases family_descends (prefixWord ++ tailWord_486757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486777 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 6]
def baseStart_486777 : Nat := 118140960795 + 486777 * 2 ^ 59
def prefixEnd_486777 : Nat := 4983230072969 + 3 ^ 40 * 486777 * 2
def baseEnd_486777 : Nat := 249950572553747216448859

theorem tailTrace_486777 : CollatzResearch.WordTrace tailWord_486777 prefixEnd_486777 249950572553747216448859 := by
  unfold tailWord_486777
  simp only [CollatzResearch.WordTrace]
  refine ⟨17754215757497538738002585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11836143838331692492001723 17754215757497538738002585)
  ·
    refine ⟨13315661818123154053501939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17754215757497538738002585 13315661818123154053501939)
    ·
      refine ⟨19973492727184731080252909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13315661818123154053501939 19973492727184731080252909)
      ·
        refine ⟨7490059772694274155094841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19973492727184731080252909 7490059772694274155094841)
        ·
          refine ⟨5617544829520705616321131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7490059772694274155094841 5617544829520705616321131)
          ·
            refine ⟨8426317244281058424481697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5617544829520705616321131 8426317244281058424481697)
            ·
              refine ⟨6319737933210793818361273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8426317244281058424481697 6319737933210793818361273)
              ·
                refine ⟨4739803449908095363770955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6319737933210793818361273 4739803449908095363770955)
                ·
                  refine ⟨7109705174862143045656433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4739803449908095363770955 7109705174862143045656433)
                  ·
                    refine ⟨5332278881146607284242325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7109705174862143045656433 5332278881146607284242325)
                    ·
                      refine ⟨249950572553747216448859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5332278881146607284242325 249950572553747216448859)
                      ·
                        rfl

theorem cell23_486777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_486777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486777 prefixEnd_486777 := by exact prefixLift 486777
  have htrace : WordTrace (prefixWord ++ tailWord_486777) baseStart_486777 baseEnd_486777 := by
    simpa [prefixWord, tailWord_486777, baseEnd_486777] using wordTrace_append hprefix tailTrace_486777
  have hstable : (prefixWord ++ tailWord_486777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486777).length < 2 ^ (prefixWord ++ tailWord_486777).sum := by decide
  have hdescent : baseEnd_486777 < baseStart_486777 := by decide
  rcases family_descends (prefixWord ++ tailWord_486777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486847 : List Nat := [1, 1, 2, 2, 2, 1, 1, 13]
def baseStart_486847 : Nat := 118140960795 + 486847 * 2 ^ 59
def prefixEnd_486847 : Nat := 4983230072969 + 3 ^ 40 * 486847 * 2
def baseEnd_486847 : Nat := 9258759859243034910131

theorem tailTrace_486847 : CollatzResearch.WordTrace tailWord_486847 prefixEnd_486847 9258759859243034910131 := by
  unfold tailWord_486847
  simp only [CollatzResearch.WordTrace]
  refine ⟨17756768867243940693050795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11837845911495960462033863 17756768867243940693050795)
  ·
    refine ⟨26635153300865911039576193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17756768867243940693050795 26635153300865911039576193)
    ·
      refine ⟨19976364975649433279682145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26635153300865911039576193 19976364975649433279682145)
      ·
        refine ⟨14982273731737074959761609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19976364975649433279682145 14982273731737074959761609)
        ·
          refine ⟨11236705298802806219821207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14982273731737074959761609 11236705298802806219821207)
          ·
            refine ⟨16855057948204209329731811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11236705298802806219821207 16855057948204209329731811)
            ·
              refine ⟨25282586922306313994597717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16855057948204209329731811 25282586922306313994597717)
              ·
                refine ⟨9258759859243034910131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 25282586922306313994597717 9258759859243034910131)
                ·
                  rfl

theorem cell23_486847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 13].length) (baseStart_486847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486847 prefixEnd_486847 := by exact prefixLift 486847
  have htrace : WordTrace (prefixWord ++ tailWord_486847) baseStart_486847 baseEnd_486847 := by
    simpa [prefixWord, tailWord_486847, baseEnd_486847] using wordTrace_append hprefix tailTrace_486847
  have hstable : (prefixWord ++ tailWord_486847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486847).length < 2 ^ (prefixWord ++ tailWord_486847).sum := by decide
  have hdescent : baseEnd_486847 < baseStart_486847 := by decide
  rcases family_descends (prefixWord ++ tailWord_486847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486852 : List Nat := [2, 3, 3, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_486852 : Nat := 118140960795 + 486852 * 2 ^ 59
def prefixEnd_486852 : Nat := 4983230072969 + 3 ^ 40 * 486852 * 2
def baseEnd_486852 : Nat := 249989083602834423011015

theorem tailTrace_486852 : CollatzResearch.WordTrace tailWord_486852 prefixEnd_486852 249989083602834423011015 := by
  unfold tailWord_486852
  simp only [CollatzResearch.WordTrace]
  refine ⟨8878475616112913273491405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11837967488150551031321873 8878475616112913273491405)
  ·
    refine ⟨3329428356042342477559277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8878475616112913273491405 3329428356042342477559277)
    ·
      refine ⟨1248535633515878429084729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3329428356042342477559277 1248535633515878429084729)
      ·
        refine ⟨936401725136908821813547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1248535633515878429084729 936401725136908821813547)
        ·
          refine ⟨1404602587705363232720321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936401725136908821813547 1404602587705363232720321)
          ·
            refine ⟨1053451940779022424540241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1404602587705363232720321 1053451940779022424540241)
            ·
              refine ⟨790088955584266818405181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053451940779022424540241 790088955584266818405181)
              ·
                refine ⟨296283358344100056901943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 790088955584266818405181 296283358344100056901943)
                ·
                  refine ⟨444425037516150085352915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296283358344100056901943 444425037516150085352915)
                  ·
                    refine ⟨666637556274225128029373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 444425037516150085352915 666637556274225128029373)
                    ·
                      refine ⟨249989083602834423011015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 666637556274225128029373 249989083602834423011015)
                      ·
                        rfl

theorem cell23_486852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_486852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486852 prefixEnd_486852 := by exact prefixLift 486852
  have htrace : WordTrace (prefixWord ++ tailWord_486852) baseStart_486852 baseEnd_486852 := by
    simpa [prefixWord, tailWord_486852, baseEnd_486852] using wordTrace_append hprefix tailTrace_486852
  have hstable : (prefixWord ++ tailWord_486852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486852).length < 2 ^ (prefixWord ++ tailWord_486852).sum := by decide
  have hdescent : baseEnd_486852 < baseStart_486852 := by decide
  rcases family_descends (prefixWord ++ tailWord_486852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486858 : List Nat := [3, 1, 2, 1, 2, 3, 4, 1, 1, 1, 4]
def baseStart_486858 : Nat := 118140960795 + 486858 * 2 ^ 59
def prefixEnd_486858 : Nat := 4983230072969 + 3 ^ 40 * 486858 * 2
def baseEnd_486858 : Nat := 249992164486761399535987

theorem tailTrace_486858 : CollatzResearch.WordTrace tailWord_486858 prefixEnd_486858 249992164486761399535987 := by
  unfold tailWord_486858
  simp only [CollatzResearch.WordTrace]
  refine ⟨4439292517551022392925307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11838113380136059714467485 4439292517551022392925307)
  ·
    refine ⟨6658938776326533589387961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4439292517551022392925307 6658938776326533589387961)
    ·
      refine ⟨4994204082244900192040971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6658938776326533589387961 4994204082244900192040971)
      ·
        refine ⟨7491306123367350288061457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4994204082244900192040971 7491306123367350288061457)
        ·
          refine ⟨5618479592525512716046093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7491306123367350288061457 5618479592525512716046093)
          ·
            refine ⟨2106929847197067268517285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5618479592525512716046093 2106929847197067268517285)
            ·
              refine ⟨395049346349450112846991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2106929847197067268517285 395049346349450112846991)
              ·
                refine ⟨592574019524175169270487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395049346349450112846991 592574019524175169270487)
                ·
                  refine ⟨888861029286262753905731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592574019524175169270487 888861029286262753905731)
                  ·
                    refine ⟨1333291543929394130858597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 888861029286262753905731 1333291543929394130858597)
                    ·
                      refine ⟨249992164486761399535987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1333291543929394130858597 249992164486761399535987)
                      ·
                        rfl

theorem cell23_486858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_486858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486858 prefixEnd_486858 := by exact prefixLift 486858
  have htrace : WordTrace (prefixWord ++ tailWord_486858) baseStart_486858 baseEnd_486858 := by
    simpa [prefixWord, tailWord_486858, baseEnd_486858] using wordTrace_append hprefix tailTrace_486858
  have hstable : (prefixWord ++ tailWord_486858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486858).length < 2 ^ (prefixWord ++ tailWord_486858).sum := by decide
  have hdescent : baseEnd_486858 < baseStart_486858 := by decide
  rcases family_descends (prefixWord ++ tailWord_486858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486868 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_486868 : Nat := 118140960795 + 486868 * 2 ^ 59
def prefixEnd_486868 : Nat := 4983230072969 + 3 ^ 40 * 486868 * 2
def baseEnd_486868 : Nat := 83332433097768786803647

theorem tailTrace_486868 : CollatzResearch.WordTrace tailWord_486868 prefixEnd_486868 83332433097768786803647 := by
  unfold tailWord_486868
  simp only [CollatzResearch.WordTrace]
  refine ⟨8878767400083930639782629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11838356533445240853043505 8878767400083930639782629)
  ·
    refine ⟨1664768887515736994959243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8878767400083930639782629 1664768887515736994959243)
    ·
      refine ⟨2497153331273605492438865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1664768887515736994959243 2497153331273605492438865)
      ·
        refine ⟨1872864998455204119329149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2497153331273605492438865 1872864998455204119329149)
        ·
          refine ⟨702324374420701544748431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1872864998455204119329149 702324374420701544748431)
          ·
            refine ⟨1053486561631052317122647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702324374420701544748431 1053486561631052317122647)
            ·
              refine ⟨1580229842446578475683971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053486561631052317122647 1580229842446578475683971)
              ·
                refine ⟨2370344763669867713525957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580229842446578475683971 2370344763669867713525957)
                ·
                  refine ⟨444439643188100196286117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2370344763669867713525957 444439643188100196286117)
                  ·
                    refine ⟨83332433097768786803647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 444439643188100196286117 83332433097768786803647)
                    ·
                      rfl

theorem cell23_486868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_486868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486868 prefixEnd_486868 := by exact prefixLift 486868
  have htrace : WordTrace (prefixWord ++ tailWord_486868) baseStart_486868 baseEnd_486868 := by
    simpa [prefixWord, tailWord_486868, baseEnd_486868] using wordTrace_append hprefix tailTrace_486868
  have hstable : (prefixWord ++ tailWord_486868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486868).length < 2 ^ (prefixWord ++ tailWord_486868).sum := by decide
  have hdescent : baseEnd_486868 < baseStart_486868 := by decide
  rcases family_descends (prefixWord ++ tailWord_486868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486885 : List Nat := [1, 3, 1, 5, 1, 2, 3, 1, 2, 4]
def baseStart_486885 : Nat := 118140960795 + 486885 * 2 ^ 59
def prefixEnd_486885 : Nat := 4983230072969 + 3 ^ 40 * 486885 * 2
def baseEnd_486885 : Nat := 83335342821477597966121

theorem tailTrace_486885 : CollatzResearch.WordTrace tailWord_486885 prefixEnd_486885 83335342821477597966121 := by
  unfold tailWord_486885
  simp only [CollatzResearch.WordTrace]
  refine ⟨17758154841106273182934109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11838769894070848788622739 17758154841106273182934109)
  ·
    refine ⟨6659308065414852443600291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17758154841106273182934109 6659308065414852443600291)
    ·
      refine ⟨9988962098122278665400437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6659308065414852443600291 9988962098122278665400437)
      ·
        refine ⟨936465196698963624881291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9988962098122278665400437 936465196698963624881291)
        ·
          refine ⟨1404697795048445437321937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936465196698963624881291 1404697795048445437321937)
          ·
            refine ⟨1053523346286334077991453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1404697795048445437321937 1053523346286334077991453)
            ·
              refine ⟨395071254857375279246795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1053523346286334077991453 395071254857375279246795)
              ·
                refine ⟨592606882286062918870193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395071254857375279246795 592606882286062918870193)
                ·
                  refine ⟨444455161714547189152645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592606882286062918870193 444455161714547189152645)
                  ·
                    refine ⟨83335342821477597966121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 444455161714547189152645 83335342821477597966121)
                    ·
                      rfl

theorem cell23_486885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_486885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486885 prefixEnd_486885 := by exact prefixLift 486885
  have htrace : WordTrace (prefixWord ++ tailWord_486885) baseStart_486885 baseEnd_486885 := by
    simpa [prefixWord, tailWord_486885, baseEnd_486885] using wordTrace_append hprefix tailTrace_486885
  have hstable : (prefixWord ++ tailWord_486885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486885).length < 2 ^ (prefixWord ++ tailWord_486885).sum := by decide
  have hdescent : baseEnd_486885 < baseStart_486885 := by decide
  rcases family_descends (prefixWord ++ tailWord_486885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486898 : List Nat := [3, 2, 1, 4, 1, 3, 2, 7]
def baseStart_486898 : Nat := 118140960795 + 486898 * 2 ^ 59
def prefixEnd_486898 : Nat := 4983230072969 + 3 ^ 40 * 486898 * 2
def baseEnd_486898 : Nat := 9259729767145971964289

theorem tailTrace_486898 : CollatzResearch.WordTrace tailWord_486898 prefixEnd_486898 9259729767145971964289 := by
  unfold tailWord_486898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4439657247514794100789337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11839085993372784268771565 4439657247514794100789337)
  ·
    refine ⟨3329742935636095575592003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4439657247514794100789337 3329742935636095575592003)
    ·
      refine ⟨4994614403454143363388005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3329742935636095575592003 4994614403454143363388005)
      ·
        refine ⟨936490200647651880635251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4994614403454143363388005 936490200647651880635251)
        ·
          refine ⟨1404735300971477820952877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936490200647651880635251 1404735300971477820952877)
          ·
            refine ⟨526775737864304182857329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1404735300971477820952877 526775737864304182857329)
            ·
              refine ⟨395081803398228137142997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526775737864304182857329 395081803398228137142997)
              ·
                refine ⟨9259729767145971964289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 395081803398228137142997 9259729767145971964289)
                ·
                  rfl

theorem cell23_486898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 7].length) (baseStart_486898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486898 prefixEnd_486898 := by exact prefixLift 486898
  have htrace : WordTrace (prefixWord ++ tailWord_486898) baseStart_486898 baseEnd_486898 := by
    simpa [prefixWord, tailWord_486898, baseEnd_486898] using wordTrace_append hprefix tailTrace_486898
  have hstable : (prefixWord ++ tailWord_486898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486898).length < 2 ^ (prefixWord ++ tailWord_486898).sum := by decide
  have hdescent : baseEnd_486898 < baseStart_486898 := by decide
  rcases family_descends (prefixWord ++ tailWord_486898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486904 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_486904 : Nat := 118140960795 + 486904 * 2 ^ 59
def prefixEnd_486904 : Nat := 4983230072969 + 3 ^ 40 * 486904 * 2
def baseEnd_486904 : Nat := 250015784596868219560775

theorem tailTrace_486904 : CollatzResearch.WordTrace tailWord_486904 prefixEnd_486904 250015784596868219560775 := by
  unfold tailWord_486904
  simp only [CollatzResearch.WordTrace]
  refine ⟨8879423914018719713937883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11839231885358292951917177 8879423914018719713937883)
  ·
    refine ⟨13319135871028079570906825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8879423914018719713937883 13319135871028079570906825)
    ·
      refine ⟨9989351903271059678180119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13319135871028079570906825 9989351903271059678180119)
      ·
        refine ⟨14984027854906589517270179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9989351903271059678180119 14984027854906589517270179)
        ·
          refine ⟨22476041782359884275905269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14984027854906589517270179 22476041782359884275905269)
          ·
            refine ⟨2107128917096239150866119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22476041782359884275905269 2107128917096239150866119)
            ·
              refine ⟨3160693375644358726299179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107128917096239150866119 3160693375644358726299179)
              ·
                refine ⟨4741040063466538089448769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160693375644358726299179 4741040063466538089448769)
                ·
                  refine ⟨3555780047599903567086577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4741040063466538089448769 3555780047599903567086577)
                  ·
                    refine ⟨2666835035699927675314933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3555780047599903567086577 2666835035699927675314933)
                    ·
                      refine ⟨250015784596868219560775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2666835035699927675314933 250015784596868219560775)
                      ·
                        rfl

theorem cell23_486904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_486904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486904 prefixEnd_486904 := by exact prefixLift 486904
  have htrace : WordTrace (prefixWord ++ tailWord_486904) baseStart_486904 baseEnd_486904 := by
    simpa [prefixWord, tailWord_486904, baseEnd_486904] using wordTrace_append hprefix tailTrace_486904
  have hstable : (prefixWord ++ tailWord_486904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486904).length < 2 ^ (prefixWord ++ tailWord_486904).sum := by decide
  have hdescent : baseEnd_486904 < baseStart_486904 := by decide
  rcases family_descends (prefixWord ++ tailWord_486904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486981 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 2, 3, 3]
def baseStart_486981 : Nat := 118140960795 + 486981 * 2 ^ 59
def prefixEnd_486981 : Nat := 4983230072969 + 3 ^ 40 * 486981 * 2
def baseEnd_486981 : Nat := 250055322607264418297921

theorem tailTrace_486981 : CollatzResearch.WordTrace tailWord_486981 prefixEnd_486981 250055322607264418297921 := by
  unfold tailWord_486981
  simp only [CollatzResearch.WordTrace]
  refine ⟨17761656248758481578428797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11841104165838987718952531 17761656248758481578428797)
  ·
    refine ⟨6660621093284430591910799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17761656248758481578428797 6660621093284430591910799)
    ·
      refine ⟨9990931639926645887866199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6660621093284430591910799 9990931639926645887866199)
      ·
        refine ⟨14986397459889968831799299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9990931639926645887866199 14986397459889968831799299)
        ·
          refine ⟨22479596189834953247698949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14986397459889968831799299 22479596189834953247698949)
          ·
            refine ⟨4214924285594053733943553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22479596189834953247698949 4214924285594053733943553)
            ·
              refine ⟨3161193214195540300457665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4214924285594053733943553 3161193214195540300457665)
              ·
                refine ⟨2370894910646655225343249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3161193214195540300457665 2370894910646655225343249)
                ·
                  refine ⟨1778171182984991419007437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2370894910646655225343249 1778171182984991419007437)
                  ·
                    refine ⟨666814193619371782127789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1778171182984991419007437 666814193619371782127789)
                    ·
                      refine ⟨250055322607264418297921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 666814193619371782127789 250055322607264418297921)
                      ·
                        rfl

theorem cell23_486981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_486981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486981 prefixEnd_486981 := by exact prefixLift 486981
  have htrace : WordTrace (prefixWord ++ tailWord_486981) baseStart_486981 baseEnd_486981 := by
    simpa [prefixWord, tailWord_486981, baseEnd_486981] using wordTrace_append hprefix tailTrace_486981
  have hstable : (prefixWord ++ tailWord_486981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486981).length < 2 ^ (prefixWord ++ tailWord_486981).sum := by decide
  have hdescent : baseEnd_486981 < baseStart_486981 := by decide
  rcases family_descends (prefixWord ++ tailWord_486981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486984 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 5, 7]
def baseStart_486984 : Nat := 118140960795 + 486984 * 2 ^ 59
def prefixEnd_486984 : Nat := 4983230072969 + 3 ^ 40 * 486984 * 2
def baseEnd_486984 : Nat := 83352287683075968853469

theorem tailTrace_486984 : CollatzResearch.WordTrace tailWord_486984 prefixEnd_486984 83352287683075968853469 := by
  unfold tailWord_486984
  simp only [CollatzResearch.WordTrace]
  refine ⟨8880882833873806545394003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11841177111831742060525337 8880882833873806545394003)
  ·
    refine ⟨13321324250810709818091005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8880882833873806545394003 13321324250810709818091005)
    ·
      refine ⟨4995496594054016181784127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13321324250810709818091005 4995496594054016181784127)
      ·
        refine ⟨7493244891081024272676191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4995496594054016181784127 7493244891081024272676191)
        ·
          refine ⟨11239867336621536409014287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7493244891081024272676191 11239867336621536409014287)
          ·
            refine ⟨16859801004932304613521431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11239867336621536409014287 16859801004932304613521431)
            ·
              refine ⟨25289701507398456920282147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16859801004932304613521431 25289701507398456920282147)
              ·
                refine ⟨37934552261097685380423221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25289701507398456920282147 37934552261097685380423221)
                ·
                  refine ⟨3556364274477908004414677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37934552261097685380423221 3556364274477908004414677)
                  ·
                    refine ⟨83352287683075968853469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3556364274477908004414677 83352287683075968853469)
                    ·
                      rfl

theorem cell23_486984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_486984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486984 prefixEnd_486984 := by exact prefixLift 486984
  have htrace : WordTrace (prefixWord ++ tailWord_486984) baseStart_486984 baseEnd_486984 := by
    simpa [prefixWord, tailWord_486984, baseEnd_486984] using wordTrace_append hprefix tailTrace_486984
  have hstable : (prefixWord ++ tailWord_486984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486984).length < 2 ^ (prefixWord ++ tailWord_486984).sum := by decide
  have hdescent : baseEnd_486984 < baseStart_486984 := by decide
  rcases family_descends (prefixWord ++ tailWord_486984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486988 : List Nat := [2, 2, 1, 3, 1, 4, 1, 4, 5]
def baseStart_486988 : Nat := 118140960795 + 486988 * 2 ^ 59
def prefixEnd_486988 : Nat := 4983230072969 + 3 ^ 40 * 486988 * 2
def baseEnd_486988 : Nat := 27784324107982876767821

theorem tailTrace_486988 : CollatzResearch.WordTrace tailWord_486988 prefixEnd_486988 27784324107982876767821 := by
  unfold tailWord_486988
  simp only [CollatzResearch.WordTrace]
  refine ⟨8880955779866560886966809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11841274373155414515955745 8880955779866560886966809)
  ·
    refine ⟨6660716834899920665225107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8880955779866560886966809 6660716834899920665225107)
    ·
      refine ⟨9991075252349880997837661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6660716834899920665225107 9991075252349880997837661)
      ·
        refine ⟨3746653219631205374189123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9991075252349880997837661 3746653219631205374189123)
        ·
          refine ⟨5619979829446808061283685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3746653219631205374189123 5619979829446808061283685)
          ·
            refine ⟨1053746218021276511490691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5619979829446808061283685 1053746218021276511490691)
            ·
              refine ⟨1580619327031914767236037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053746218021276511490691 1580619327031914767236037)
              ·
                refine ⟨296366123818484018856757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1580619327031914767236037 296366123818484018856757)
                ·
                  refine ⟨27784324107982876767821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 296366123818484018856757 27784324107982876767821)
                  ·
                    rfl

theorem cell23_486988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 5].length) (baseStart_486988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_486988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_486988 prefixEnd_486988 := by exact prefixLift 486988
  have htrace : WordTrace (prefixWord ++ tailWord_486988) baseStart_486988 baseEnd_486988 := by
    simpa [prefixWord, tailWord_486988, baseEnd_486988] using wordTrace_append hprefix tailTrace_486988
  have hstable : (prefixWord ++ tailWord_486988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486988).length < 2 ^ (prefixWord ++ tailWord_486988).sum := by decide
  have hdescent : baseEnd_486988 < baseStart_486988 := by decide
  rcases family_descends (prefixWord ++ tailWord_486988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487005 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 7]
def baseStart_487005 : Nat := 118140960795 + 487005 * 2 ^ 59
def prefixEnd_487005 : Nat := 4983230072969 + 3 ^ 40 * 487005 * 2
def baseEnd_487005 : Nat := 27785294015885813821979

theorem tailTrace_487005 : CollatzResearch.WordTrace tailWord_487005 prefixEnd_487005 27785294015885813821979 := by
  unfold tailWord_487005
  simp only [CollatzResearch.WordTrace]
  refine ⟨17762531600671533677302469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11841687733781022451534979 17762531600671533677302469)
  ·
    refine ⟨3330474675125912564494213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17762531600671533677302469 3330474675125912564494213)
    ·
      refine ⟨624464001586108605842665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3330474675125912564494213 624464001586108605842665)
      ·
        refine ⟨468348001189581454381999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624464001586108605842665 468348001189581454381999)
        ·
          refine ⟨702522001784372181572999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468348001189581454381999 702522001784372181572999)
          ·
            refine ⟨1053783002676558272359499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702522001784372181572999 1053783002676558272359499)
            ·
              refine ⟨1580674504014837408539249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053783002676558272359499 1580674504014837408539249)
              ·
                refine ⟨1185505878011128056404437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580674504014837408539249 1185505878011128056404437)
                ·
                  refine ⟨27785294015885813821979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1185505878011128056404437 27785294015885813821979)
                  ·
                    rfl

theorem cell23_487005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_487005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487005 prefixEnd_487005 := by exact prefixLift 487005
  have htrace : WordTrace (prefixWord ++ tailWord_487005) baseStart_487005 baseEnd_487005 := by
    simpa [prefixWord, tailWord_487005, baseEnd_487005] using wordTrace_append hprefix tailTrace_487005
  have hstable : (prefixWord ++ tailWord_487005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487005).length < 2 ^ (prefixWord ++ tailWord_487005).sum := by decide
  have hdescent : baseEnd_487005 < baseStart_487005 := by decide
  rcases family_descends (prefixWord ++ tailWord_487005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487018 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 2, 5]
def baseStart_487018 : Nat := 118140960795 + 487018 * 2 ^ 59
def prefixEnd_487018 : Nat := 4983230072969 + 3 ^ 40 * 487018 * 2
def baseEnd_487018 : Nat := 83358107130493591178417

theorem tailTrace_487018 : CollatzResearch.WordTrace tailWord_487018 prefixEnd_487018 83358107130493591178417 := by
  unfold tailWord_487018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4440751437406109224381427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11842003833082957931683805 4440751437406109224381427)
  ·
    refine ⟨6661127156109163836572141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4440751437406109224381427 6661127156109163836572141)
    ·
      refine ⟨2497922683540936438714553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6661127156109163836572141 2497922683540936438714553)
      ·
        refine ⟨1873442012655702329035915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2497922683540936438714553 1873442012655702329035915)
        ·
          refine ⟨2810163018983553493553873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873442012655702329035915 2810163018983553493553873)
          ·
            refine ⟨2107622264237665120165405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2810163018983553493553873 2107622264237665120165405)
            ·
              refine ⟨790358349089124420062027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2107622264237665120165405 790358349089124420062027)
              ·
                refine ⟨1185537523633686630093041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790358349089124420062027 1185537523633686630093041)
                ·
                  refine ⟨889153142725264972569781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1185537523633686630093041 889153142725264972569781)
                  ·
                    refine ⟨83358107130493591178417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 889153142725264972569781 83358107130493591178417)
                    ·
                      rfl

theorem cell23_487018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_487018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487018 prefixEnd_487018 := by exact prefixLift 487018
  have htrace : WordTrace (prefixWord ++ tailWord_487018) baseStart_487018 baseEnd_487018 := by
    simpa [prefixWord, tailWord_487018, baseEnd_487018] using wordTrace_append hprefix tailTrace_487018
  have hstable : (prefixWord ++ tailWord_487018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487018).length < 2 ^ (prefixWord ++ tailWord_487018).sum := by decide
  have hdescent : baseEnd_487018 < baseStart_487018 := by decide
  rcases family_descends (prefixWord ++ tailWord_487018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487031 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 7, 4]
def baseStart_487031 : Nat := 118140960795 + 487031 * 2 ^ 59
def prefixEnd_487031 : Nat := 4983230072969 + 3 ^ 40 * 487031 * 2
def baseEnd_487031 : Nat := 83360332213329740890897

theorem tailTrace_487031 : CollatzResearch.WordTrace tailWord_487031 prefixEnd_487031 83360332213329740890897 := by
  unfold tailWord_487031
  simp only [CollatzResearch.WordTrace]
  refine ⟨17763479898577340117748947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11842319932384893411832631 17763479898577340117748947)
  ·
    refine ⟨26645219847866010176623421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17763479898577340117748947 26645219847866010176623421)
    ·
      refine ⟨9991957442949753816233783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26645219847866010176623421 9991957442949753816233783)
      ·
        refine ⟨14987936164424630724350675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9991957442949753816233783 14987936164424630724350675)
        ·
          refine ⟨22481904246636946086526013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14987936164424630724350675 22481904246636946086526013)
          ·
            refine ⟨8430714092488854782447255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22481904246636946086526013 8430714092488854782447255)
            ·
              refine ⟨12646071138733282173670883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8430714092488854782447255 12646071138733282173670883)
              ·
                refine ⟨18969106708099923260506325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12646071138733282173670883 18969106708099923260506325)
                ·
                  refine ⟨444588438471091951418117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18969106708099923260506325 444588438471091951418117)
                  ·
                    refine ⟨83360332213329740890897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 444588438471091951418117 83360332213329740890897)
                    ·
                      rfl

theorem cell23_487031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_487031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487031 prefixEnd_487031 := by exact prefixLift 487031
  have htrace : WordTrace (prefixWord ++ tailWord_487031) baseStart_487031 baseEnd_487031 := by
    simpa [prefixWord, tailWord_487031, baseEnd_487031] using wordTrace_append hprefix tailTrace_487031
  have hstable : (prefixWord ++ tailWord_487031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487031).length < 2 ^ (prefixWord ++ tailWord_487031).sum := by decide
  have hdescent : baseEnd_487031 < baseStart_487031 := by decide
  rcases family_descends (prefixWord ++ tailWord_487031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487061 : List Nat := [1, 3, 2, 1, 1, 1, 1, 7, 6]
def baseStart_487061 : Nat := 118140960795 + 487061 * 2 ^ 59
def prefixEnd_487061 : Nat := 4983230072969 + 3 ^ 40 * 487061 * 2
def baseEnd_487061 : Nat := 27788489006624900588617

theorem tailTrace_487061 : CollatzResearch.WordTrace tailWord_487061 prefixEnd_487061 27788489006624900588617 := by
  unfold tailWord_487061
  simp only [CollatzResearch.WordTrace]
  refine ⟨17764574088468655241341037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11843049392312436827560691 17764574088468655241341037)
  ·
    refine ⟨6661715283175745715502889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17764574088468655241341037 6661715283175745715502889)
    ·
      refine ⟨4996286462381809286627167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6661715283175745715502889 4996286462381809286627167)
      ·
        refine ⟨7494429693572713929940751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4996286462381809286627167 7494429693572713929940751)
        ·
          refine ⟨11241644540359070894911127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7494429693572713929940751 11241644540359070894911127)
          ·
            refine ⟨16862466810538606342366691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11241644540359070894911127 16862466810538606342366691)
            ·
              refine ⟨25293700215807909513550037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16862466810538606342366691 25293700215807909513550037)
              ·
                refine ⟨592821098807997879223829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25293700215807909513550037 592821098807997879223829)
                ·
                  refine ⟨27788489006624900588617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 592821098807997879223829 27788489006624900588617)
                  ·
                    rfl

theorem cell23_487061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 6].length) (baseStart_487061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487061 prefixEnd_487061 := by exact prefixLift 487061
  have htrace : WordTrace (prefixWord ++ tailWord_487061) baseStart_487061 baseEnd_487061 := by
    simpa [prefixWord, tailWord_487061, baseEnd_487061] using wordTrace_append hprefix tailTrace_487061
  have hstable : (prefixWord ++ tailWord_487061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487061).length < 2 ^ (prefixWord ++ tailWord_487061).sum := by decide
  have hdescent : baseEnd_487061 < baseStart_487061 := by decide
  rcases family_descends (prefixWord ++ tailWord_487061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487088 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 5, 1, 3]
def baseStart_487088 : Nat := 118140960795 + 487088 * 2 ^ 59
def prefixEnd_487088 : Nat := 4983230072969 + 3 ^ 40 * 487088 * 2
def baseEnd_487088 : Nat := 250110265037295499659929

theorem tailTrace_487088 : CollatzResearch.WordTrace tailWord_487088 prefixEnd_487088 250110265037295499659929 := by
  unfold tailWord_487088
  simp only [CollatzResearch.WordTrace]
  refine ⟨8882779429685419426286959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11843705906247225901715945 8882779429685419426286959)
  ·
    refine ⟨13324169144528129139430439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8882779429685419426286959 13324169144528129139430439)
    ·
      refine ⟨19986253716792193709145659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13324169144528129139430439 19986253716792193709145659)
      ·
        refine ⟨29979380575188290563718489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19986253716792193709145659 29979380575188290563718489)
        ·
          refine ⟨22484535431391217922788867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29979380575188290563718489 22484535431391217922788867)
          ·
            refine ⟨33726803147086826884183301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22484535431391217922788867 33726803147086826884183301)
            ·
              refine ⟨6323775590078780040784369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33726803147086826884183301 6323775590078780040784369)
              ·
                refine ⟨4742831692559085030588277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6323775590078780040784369 4742831692559085030588277)
                ·
                  refine ⟨444640471177414221617651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4742831692559085030588277 444640471177414221617651)
                  ·
                    refine ⟨666960706766121332426477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 444640471177414221617651 666960706766121332426477)
                    ·
                      refine ⟨250110265037295499659929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 666960706766121332426477 250110265037295499659929)
                      ·
                        rfl

theorem cell23_487088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 5, 1, 3].length) (baseStart_487088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487088 prefixEnd_487088 := by exact prefixLift 487088
  have htrace : WordTrace (prefixWord ++ tailWord_487088) baseStart_487088 baseEnd_487088 := by
    simpa [prefixWord, tailWord_487088, baseEnd_487088] using wordTrace_append hprefix tailTrace_487088
  have hstable : (prefixWord ++ tailWord_487088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487088).length < 2 ^ (prefixWord ++ tailWord_487088).sum := by decide
  have hdescent : baseEnd_487088 < baseStart_487088 := by decide
  rcases family_descends (prefixWord ++ tailWord_487088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487108 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_487108 : Nat := 118140960795 + 487108 * 2 ^ 59
def prefixEnd_487108 : Nat := 4983230072969 + 3 ^ 40 * 487108 * 2
def baseEnd_487108 : Nat := 83373511550128473803279

theorem tailTrace_487108 : CollatzResearch.WordTrace tailWord_487108 prefixEnd_487108 83373511550128473803279 := by
  unfold tailWord_487108
  simp only [CollatzResearch.WordTrace]
  refine ⟨8883144159649191134150989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11844192212865588178867985 8883144159649191134150989)
  ·
    refine ⟨3331179059868446675306621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8883144159649191134150989 3331179059868446675306621)
    ·
      refine ⟨1249192147450667503239983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3331179059868446675306621 1249192147450667503239983)
      ·
        refine ⟨1873788221176001254859975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249192147450667503239983 1873788221176001254859975)
        ·
          refine ⟨2810682331764001882289963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873788221176001254859975 2810682331764001882289963)
          ·
            refine ⟨4216023497646002823434945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810682331764001882289963 4216023497646002823434945)
            ·
              refine ⟨3162017623234502117576209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4216023497646002823434945 3162017623234502117576209)
              ·
                refine ⟨2371513217425876588182157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3162017623234502117576209 2371513217425876588182157)
                ·
                  refine ⟨889317456534703720568309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2371513217425876588182157 889317456534703720568309)
                  ·
                    refine ⟨83373511550128473803279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 889317456534703720568309 83373511550128473803279)
                    ·
                      rfl

theorem cell23_487108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_487108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487108 prefixEnd_487108 := by exact prefixLift 487108
  have htrace : WordTrace (prefixWord ++ tailWord_487108) baseStart_487108 baseEnd_487108 := by
    simpa [prefixWord, tailWord_487108, baseEnd_487108] using wordTrace_append hprefix tailTrace_487108
  have hstable : (prefixWord ++ tailWord_487108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487108).length < 2 ^ (prefixWord ++ tailWord_487108).sum := by decide
  have hdescent : baseEnd_487108 < baseStart_487108 := by decide
  rcases family_descends (prefixWord ++ tailWord_487108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487128 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 3, 1, 4]
def baseStart_487128 : Nat := 118140960795 + 487128 * 2 ^ 59
def prefixEnd_487128 : Nat := 4983230072969 + 3 ^ 40 * 487128 * 2
def baseEnd_487128 : Nat := 250130804263475343159745

theorem tailTrace_487128 : CollatzResearch.WordTrace tailWord_487128 prefixEnd_487128 250130804263475343159745 := by
  unfold tailWord_487128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8883508889612962842015019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11844678519483950456020025 8883508889612962842015019)
  ·
    refine ⟨13325263334419444263022529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8883508889612962842015019 13325263334419444263022529)
    ·
      refine ⟨9993947500814583197266897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13325263334419444263022529 9993947500814583197266897)
      ·
        refine ⟨7495460625610937397950173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9993947500814583197266897 7495460625610937397950173)
        ·
          refine ⟨2810797734604101524231315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7495460625610937397950173 2810797734604101524231315)
          ·
            refine ⟨4216196601906152286346973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810797734604101524231315 4216196601906152286346973)
            ·
              refine ⟨1581073725714807107380115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4216196601906152286346973 1581073725714807107380115)
              ·
                refine ⟨2371610588572210661070173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581073725714807107380115 2371610588572210661070173)
                ·
                  refine ⟨889353970714578997901315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2371610588572210661070173 889353970714578997901315)
                  ·
                    refine ⟨1334030956071868496851973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 889353970714578997901315 1334030956071868496851973)
                    ·
                      refine ⟨250130804263475343159745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1334030956071868496851973 250130804263475343159745)
                      ·
                        rfl

theorem cell23_487128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_487128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487128 prefixEnd_487128 := by exact prefixLift 487128
  have htrace : WordTrace (prefixWord ++ tailWord_487128) baseStart_487128 baseEnd_487128 := by
    simpa [prefixWord, tailWord_487128, baseEnd_487128] using wordTrace_append hprefix tailTrace_487128
  have hstable : (prefixWord ++ tailWord_487128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487128).length < 2 ^ (prefixWord ++ tailWord_487128).sum := by decide
  have hdescent : baseEnd_487128 < baseStart_487128 := by decide
  rcases family_descends (prefixWord ++ tailWord_487128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487148 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 5]
def baseStart_487148 : Nat := 118140960795 + 487148 * 2 ^ 59
def prefixEnd_487148 : Nat := 4983230072969 + 3 ^ 40 * 487148 * 2
def baseEnd_487148 : Nat := 250141073876565264909653

theorem tailTrace_487148 : CollatzResearch.WordTrace tailWord_487148 prefixEnd_487148 250141073876565264909653 := by
  unfold tailWord_487148
  simp only [CollatzResearch.WordTrace]
  refine ⟨8883873619576734549879049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11845164826102312733172065 8883873619576734549879049)
  ·
    refine ⟨6662905214682550912409287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8883873619576734549879049 6662905214682550912409287)
    ·
      refine ⟨9994357822023826368613931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6662905214682550912409287 9994357822023826368613931)
      ·
        refine ⟨14991536733035739552920897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9994357822023826368613931 14991536733035739552920897)
        ·
          refine ⟨11243652549776804664690673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14991536733035739552920897 11243652549776804664690673)
          ·
            refine ⟨8432739412332603498518005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11243652549776804664690673 8432739412332603498518005)
            ·
              refine ⟨790569319906181577986063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8432739412332603498518005 790569319906181577986063)
              ·
                refine ⟨1185853979859272366979095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790569319906181577986063 1185853979859272366979095)
                ·
                  refine ⟨1778780969788908550468643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185853979859272366979095 1778780969788908550468643)
                  ·
                    refine ⟨2668171454683362825702965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1778780969788908550468643 2668171454683362825702965)
                    ·
                      refine ⟨250141073876565264909653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2668171454683362825702965 250141073876565264909653)
                      ·
                        rfl

theorem cell23_487148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_487148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487148 prefixEnd_487148 := by exact prefixLift 487148
  have htrace : WordTrace (prefixWord ++ tailWord_487148) baseStart_487148 baseEnd_487148 := by
    simpa [prefixWord, tailWord_487148, baseEnd_487148] using wordTrace_append hprefix tailTrace_487148
  have hstable : (prefixWord ++ tailWord_487148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487148).length < 2 ^ (prefixWord ++ tailWord_487148).sum := by decide
  have hdescent : baseEnd_487148 < baseStart_487148 := by decide
  rcases family_descends (prefixWord ++ tailWord_487148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487171 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 6]
def baseStart_487171 : Nat := 118140960795 + 487171 * 2 ^ 59
def prefixEnd_487171 : Nat := 4983230072969 + 3 ^ 40 * 487171 * 2
def baseEnd_487171 : Nat := 250152883931618674922047

theorem tailTrace_487171 : CollatzResearch.WordTrace tailWord_487171 prefixEnd_487171 250152883931618674922047 := by
  unfold tailWord_487171
  simp only [CollatzResearch.WordTrace]
  refine ⟨17768586118070144027845367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11845724078713429351896911 17768586118070144027845367)
  ·
    refine ⟨26652879177105216041768051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17768586118070144027845367 26652879177105216041768051)
    ·
      refine ⟨39979318765657824062652077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26652879177105216041768051 39979318765657824062652077)
      ·
        refine ⟨14992244537121684023494529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39979318765657824062652077 14992244537121684023494529)
        ·
          refine ⟨11244183402841263017620897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14992244537121684023494529 11244183402841263017620897)
          ·
            refine ⟨8433137552130947263215673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11244183402841263017620897 8433137552130947263215673)
            ·
              refine ⟨6324853164098210447411755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8433137552130947263215673 6324853164098210447411755)
              ·
                refine ⟨9487279746147315671117633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6324853164098210447411755 9487279746147315671117633)
                ·
                  refine ⟨7115459809610486753338225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9487279746147315671117633 7115459809610486753338225)
                  ·
                    refine ⟨5336594857207865065003669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7115459809610486753338225 5336594857207865065003669)
                    ·
                      refine ⟨250152883931618674922047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5336594857207865065003669 250152883931618674922047)
                      ·
                        rfl

theorem cell23_487171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_487171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487171 prefixEnd_487171 := by exact prefixLift 487171
  have htrace : WordTrace (prefixWord ++ tailWord_487171) baseStart_487171 baseEnd_487171 := by
    simpa [prefixWord, tailWord_487171, baseEnd_487171] using wordTrace_append hprefix tailTrace_487171
  have hstable : (prefixWord ++ tailWord_487171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487171).length < 2 ^ (prefixWord ++ tailWord_487171).sum := by decide
  have hdescent : baseEnd_487171 < baseStart_487171 := by decide
  rcases family_descends (prefixWord ++ tailWord_487171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
