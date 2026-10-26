import V185TrunkScan23Chunk1263

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7487292 : List Nat := [2, 2, 2, 2, 1, 1, 3, 4, 1, 3, 2]
def baseStart_7487292 : Nat := 118140960795 + 7487292 * 2 ^ 59
def prefixEnd_7487292 : Nat := 4983230072969 + 3 ^ 40 * 7487292 * 2
def baseEnd_7487292 : Nat := 3844579596563425169316577

theorem tailTrace_7487292 : CollatzResearch.WordTrace tailWord_7487292 prefixEnd_7487292 3844579596563425169316577 := by
  unfold tailWord_7487292
  simp only [CollatzResearch.WordTrace]
  refine ⟨136541986995413643257000065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182055982660551524342666753 136541986995413643257000065)
  ·
    refine ⟨102406490246560232442750049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136541986995413643257000065 102406490246560232442750049)
    ·
      refine ⟨76804867684920174332062537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102406490246560232442750049 76804867684920174332062537)
      ·
        refine ⟨57603650763690130749046903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76804867684920174332062537 57603650763690130749046903)
        ·
          refine ⟨86405476145535196123570355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57603650763690130749046903 86405476145535196123570355)
          ·
            refine ⟨129608214218302794185355533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86405476145535196123570355 129608214218302794185355533)
            ·
              refine ⟨48603080331863547819508325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129608214218302794185355533 48603080331863547819508325)
              ·
                refine ⟨9113077562224415216157811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48603080331863547819508325 9113077562224415216157811)
                ·
                  refine ⟨13669616343336622824236717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9113077562224415216157811 13669616343336622824236717)
                  ·
                    refine ⟨5126106128751233559088769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13669616343336622824236717 5126106128751233559088769)
                    ·
                      refine ⟨3844579596563425169316577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5126106128751233559088769 3844579596563425169316577)
                      ·
                        rfl

theorem cell23_7487292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_7487292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487292 prefixEnd_7487292 := by exact prefixLift 7487292
  have htrace : WordTrace (prefixWord ++ tailWord_7487292) baseStart_7487292 baseEnd_7487292 := by
    simpa [prefixWord, tailWord_7487292, baseEnd_7487292] using wordTrace_append hprefix tailTrace_7487292
  have hstable : (prefixWord ++ tailWord_7487292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487292).length < 2 ^ (prefixWord ++ tailWord_7487292).sum := by decide
  have hdescent : baseEnd_7487292 < baseStart_7487292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487305 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 3, 4, 2]
def baseStart_7487305 : Nat := 118140960795 + 7487305 * 2 ^ 59
def prefixEnd_7487305 : Nat := 4983230072969 + 3 ^ 40 * 7487305 * 2
def baseEnd_7487305 : Nat := 3844586271811933618454017

theorem tailTrace_7487305 : CollatzResearch.WordTrace tailWord_7487305 prefixEnd_7487305 3844586271811933618454017 := by
  unfold tailWord_7487305
  simp only [CollatzResearch.WordTrace]
  refine ⟨273084448139780189734223369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182056298759853459822815579 273084448139780189734223369)
  ·
    refine ⟨204813336104835142300667527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273084448139780189734223369 204813336104835142300667527)
    ·
      refine ⟨307220004157252713451001291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204813336104835142300667527 307220004157252713451001291)
      ·
        refine ⟨460830006235879070176501937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307220004157252713451001291 460830006235879070176501937)
        ·
          refine ⟨345622504676909302632376453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460830006235879070176501937 345622504676909302632376453)
          ·
            refine ⟨64804219626920494243570585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 345622504676909302632376453 64804219626920494243570585)
            ·
              refine ⟨48603164720190370682677939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64804219626920494243570585 48603164720190370682677939)
              ·
                refine ⟨72904747080285556024016909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48603164720190370682677939 72904747080285556024016909)
                ·
                  refine ⟨27339280155107083509006341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72904747080285556024016909 27339280155107083509006341)
                  ·
                    refine ⟨5126115029082578157938689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27339280155107083509006341 5126115029082578157938689)
                    ·
                      refine ⟨3844586271811933618454017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5126115029082578157938689 3844586271811933618454017)
                      ·
                        rfl

theorem cell23_7487305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 4, 2].length) (baseStart_7487305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487305 prefixEnd_7487305 := by exact prefixLift 7487305
  have htrace : WordTrace (prefixWord ++ tailWord_7487305) baseStart_7487305 baseEnd_7487305 := by
    simpa [prefixWord, tailWord_7487305, baseEnd_7487305] using wordTrace_append hprefix tailTrace_7487305
  have hstable : (prefixWord ++ tailWord_7487305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487305).length < 2 ^ (prefixWord ++ tailWord_7487305).sum := by decide
  have hdescent : baseEnd_7487305 < baseStart_7487305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487322 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2]
def baseStart_7487322 : Nat := 118140960795 + 7487322 * 2 ^ 59
def prefixEnd_7487322 : Nat := 4983230072969 + 3 ^ 40 * 7487322 * 2
def baseEnd_7487322 : Nat := 3844595000983060051941439

theorem tailTrace_7487322 : CollatzResearch.WordTrace tailWord_7487322 prefixEnd_7487322 3844595000983060051941439 := by
  unfold tailWord_7487322
  simp only [CollatzResearch.WordTrace]
  refine ⟨68271267045179650409398055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182056712120479067758394813 68271267045179650409398055)
  ·
    refine ⟨102406900567769475614097083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68271267045179650409398055 102406900567769475614097083)
    ·
      refine ⟨153610350851654213421145625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102406900567769475614097083 153610350851654213421145625)
      ·
        refine ⟨115207763138740660065859219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153610350851654213421145625 115207763138740660065859219)
        ·
          refine ⟨172811644708110990098788829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115207763138740660065859219 172811644708110990098788829)
          ·
            refine ⟨64804366765541621287045811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172811644708110990098788829 64804366765541621287045811)
            ·
              refine ⟨97206550148312431930568717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64804366765541621287045811 97206550148312431930568717)
              ·
                refine ⟨36452456305617161973963269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97206550148312431930568717 36452456305617161973963269)
                ·
                  refine ⟨6834835557303217870118113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36452456305617161973963269 6834835557303217870118113)
                  ·
                    refine ⟨5126126667977413402588585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6834835557303217870118113 5126126667977413402588585)
                    ·
                      refine ⟨3844595000983060051941439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5126126667977413402588585 3844595000983060051941439)
                      ·
                        rfl

theorem cell23_7487322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_7487322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487322 prefixEnd_7487322 := by exact prefixLift 7487322
  have htrace : WordTrace (prefixWord ++ tailWord_7487322) baseStart_7487322 baseEnd_7487322 := by
    simpa [prefixWord, tailWord_7487322, baseEnd_7487322] using wordTrace_append hprefix tailTrace_7487322
  have hstable : (prefixWord ++ tailWord_7487322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487322).length < 2 ^ (prefixWord ++ tailWord_7487322).sum := by decide
  have hdescent : baseEnd_7487322 < baseStart_7487322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487408 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 6]
def baseStart_7487408 : Nat := 118140960795 + 7487408 * 2 ^ 59
def prefixEnd_7487408 : Nat := 4983230072969 + 3 ^ 40 * 7487408 * 2
def baseEnd_7487408 : Nat := 3844639160319346715466043

theorem tailTrace_7487408 : CollatzResearch.WordTrace tailWord_7487408 prefixEnd_7487408 3844639160319346715466043 := by
  unfold tailWord_7487408
  simp only [CollatzResearch.WordTrace]
  refine ⟨136544102429203519162611439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182058803238938025550148585 136544102429203519162611439)
  ·
    refine ⟨204816153643805278743917159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136544102429203519162611439 204816153643805278743917159)
    ·
      refine ⟨307224230465707918115875739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204816153643805278743917159 307224230465707918115875739)
      ·
        refine ⟨460836345698561877173813609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307224230465707918115875739 460836345698561877173813609)
        ·
          refine ⟨345627259273921407880360207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460836345698561877173813609 345627259273921407880360207)
          ·
            refine ⟨518440888910882111820540311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345627259273921407880360207 518440888910882111820540311)
            ·
              refine ⟨777661333366323167730810467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518440888910882111820540311 777661333366323167730810467)
              ·
                refine ⟨1166492000049484751596215701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777661333366323167730810467 1166492000049484751596215701)
                ·
                  refine ⟨54679312502319597731072611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1166492000049484751596215701 54679312502319597731072611)
                  ·
                    refine ⟨82018968753479396596608917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54679312502319597731072611 82018968753479396596608917)
                    ·
                      refine ⟨3844639160319346715466043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82018968753479396596608917 3844639160319346715466043)
                      ·
                        rfl

theorem cell23_7487408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_7487408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487408 prefixEnd_7487408 := by exact prefixLift 7487408
  have htrace : WordTrace (prefixWord ++ tailWord_7487408) baseStart_7487408 baseEnd_7487408 := by
    simpa [prefixWord, tailWord_7487408, baseEnd_7487408] using wordTrace_append hprefix tailTrace_7487408
  have hstable : (prefixWord ++ tailWord_7487408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487408).length < 2 ^ (prefixWord ++ tailWord_7487408).sum := by decide
  have hdescent : baseEnd_7487408 < baseStart_7487408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487472 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 1, 5, 2]
def baseStart_7487472 : Nat := 118140960795 + 7487472 * 2 ^ 59
def prefixEnd_7487472 : Nat := 4983230072969 + 3 ^ 40 * 7487472 * 2
def baseEnd_7487472 : Nat := 3844672023081234465065749

theorem tailTrace_7487472 : CollatzResearch.WordTrace tailWord_7487472 prefixEnd_7487472 3844672023081234465065749 := by
  unfold tailWord_7487472
  simp only [CollatzResearch.WordTrace]
  refine ⟨136545269565087588627776335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182060359420116784837035113 136545269565087588627776335)
  ·
    refine ⟨204817904347631382941664503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136545269565087588627776335 204817904347631382941664503)
    ·
      refine ⟨307226856521447074412496755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204817904347631382941664503 307226856521447074412496755)
      ·
        refine ⟨460840284782170611618745133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307226856521447074412496755 460840284782170611618745133)
        ·
          refine ⟨172815106793313979357029425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460840284782170611618745133 172815106793313979357029425)
          ·
            refine ⟨129611330094985484517772069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172815106793313979357029425 129611330094985484517772069)
            ·
              refine ⟨24302124392809778347082263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129611330094985484517772069 24302124392809778347082263)
              ·
                refine ⟨36453186589214667520623395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24302124392809778347082263 36453186589214667520623395)
                ·
                  refine ⟨54679779883822001280935093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36453186589214667520623395 54679779883822001280935093)
                  ·
                    refine ⟨5126229364108312620087665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54679779883822001280935093 5126229364108312620087665)
                    ·
                      refine ⟨3844672023081234465065749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5126229364108312620087665 3844672023081234465065749)
                      ·
                        rfl

theorem cell23_7487472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 5, 2].length) (baseStart_7487472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487472 prefixEnd_7487472 := by exact prefixLift 7487472
  have htrace : WordTrace (prefixWord ++ tailWord_7487472) baseStart_7487472 baseEnd_7487472 := by
    simpa [prefixWord, tailWord_7487472, baseEnd_7487472] using wordTrace_append hprefix tailTrace_7487472
  have hstable : (prefixWord ++ tailWord_7487472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487472).length < 2 ^ (prefixWord ++ tailWord_7487472).sum := by decide
  have hdescent : baseEnd_7487472 < baseStart_7487472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487473 : List Nat := [1, 2, 2, 2, 6, 1, 1, 3, 1, 4]
def baseStart_7487473 : Nat := 118140960795 + 7487473 * 2 ^ 59
def prefixEnd_7487473 : Nat := 4983230072969 + 3 ^ 40 * 7487473 * 2
def baseEnd_7487473 : Nat := 1281557512187296320384415

theorem tailTrace_7487473 : CollatzResearch.WordTrace tailWord_7487473 prefixEnd_7487473 1281557512187296320384415 := by
  unfold tailWord_7487473
  simp only [CollatzResearch.WordTrace]
  refine ⟨273090575603171554426339073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182060383735447702950892715 273090575603171554426339073)
  ·
    refine ⟨204817931702378665819754305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273090575603171554426339073 204817931702378665819754305)
    ·
      refine ⟨153613448776783999364815729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204817931702378665819754305 153613448776783999364815729)
      ·
        refine ⟨115210086582587999523611797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153613448776783999364815729 115210086582587999523611797)
        ·
          refine ⟨5400472808558812477669303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115210086582587999523611797 5400472808558812477669303)
          ·
            refine ⟨8100709212838218716503955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5400472808558812477669303 8100709212838218716503955)
            ·
              refine ⟨12151063819257328074755933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8100709212838218716503955 12151063819257328074755933)
              ·
                refine ⟨4556648932221498028033475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12151063819257328074755933 4556648932221498028033475)
                ·
                  refine ⟨6834973398332247042050213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556648932221498028033475 6834973398332247042050213)
                  ·
                    refine ⟨1281557512187296320384415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6834973398332247042050213 1281557512187296320384415)
                    ·
                      rfl

theorem cell23_7487473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_7487473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487473 prefixEnd_7487473 := by exact prefixLift 7487473
  have htrace : WordTrace (prefixWord ++ tailWord_7487473) baseStart_7487473 baseEnd_7487473 := by
    simpa [prefixWord, tailWord_7487473, baseEnd_7487473] using wordTrace_append hprefix tailTrace_7487473
  have hstable : (prefixWord ++ tailWord_7487473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487473).length < 2 ^ (prefixWord ++ tailWord_7487473).sum := by decide
  have hdescent : baseEnd_7487473 < baseStart_7487473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487489 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_7487489 : Nat := 118140960795 + 7487489 * 2 ^ 59
def prefixEnd_7487489 : Nat := 4983230072969 + 3 ^ 40 * 7487489 * 2
def baseEnd_7487489 : Nat := 3844680752252360898553171

theorem tailTrace_7487489 : CollatzResearch.WordTrace tailWord_7487489 prefixEnd_7487489 3844680752252360898553171 := by
  unfold tailWord_7487489
  simp only [CollatzResearch.WordTrace]
  refine ⟨273091159171113589158921521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182060772780742392772614347 273091159171113589158921521)
  ·
    refine ⟨204818369378335191869191141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273091159171113589158921521 204818369378335191869191141)
    ·
      refine ⟨38403444258437848475473339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204818369378335191869191141 38403444258437848475473339)
      ·
        refine ⟨57605166387656772713210009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38403444258437848475473339 57605166387656772713210009)
        ·
          refine ⟨43203874790742579534907507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57605166387656772713210009 43203874790742579534907507)
          ·
            refine ⟨64805812186113869302361261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43203874790742579534907507 64805812186113869302361261)
            ·
              refine ⟨24302179569792700988385473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64805812186113869302361261 24302179569792700988385473)
              ·
                refine ⟨18226634677344525741289105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24302179569792700988385473 18226634677344525741289105)
                ·
                  refine ⟨13669976008008394305966829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18226634677344525741289105 13669976008008394305966829)
                  ·
                    refine ⟨5126241003003147864737561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13669976008008394305966829 5126241003003147864737561)
                    ·
                      refine ⟨3844680752252360898553171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5126241003003147864737561 3844680752252360898553171)
                      ·
                        rfl

theorem cell23_7487489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_7487489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487489 prefixEnd_7487489 := by exact prefixLift 7487489
  have htrace : WordTrace (prefixWord ++ tailWord_7487489) baseStart_7487489 baseEnd_7487489 := by
    simpa [prefixWord, tailWord_7487489, baseEnd_7487489] using wordTrace_append hprefix tailTrace_7487489
  have hstable : (prefixWord ++ tailWord_7487489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487489).length < 2 ^ (prefixWord ++ tailWord_7487489).sum := by decide
  have hdescent : baseEnd_7487489 < baseStart_7487489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487502 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_7487502 : Nat := 118140960795 + 7487502 * 2 ^ 59
def prefixEnd_7487502 : Nat := 4983230072969 + 3 ^ 40 * 7487502 * 2
def baseEnd_7487502 : Nat := 3844687427500869347690611

theorem tailTrace_7487502 : CollatzResearch.WordTrace tailWord_7487502 prefixEnd_7487502 3844687427500869347690611 := by
  unfold tailWord_7487502
  simp only [CollatzResearch.WordTrace]
  refine ⟨34136454165008311547393095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182061088880044328252763173 34136454165008311547393095)
  ·
    refine ⟨51204681247512467321089643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34136454165008311547393095 51204681247512467321089643)
    ·
      refine ⟨76807021871268700981634465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51204681247512467321089643 76807021871268700981634465)
      ·
        refine ⟨57605266403451525736225849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76807021871268700981634465 57605266403451525736225849)
        ·
          refine ⟨43203949802588644302169387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57605266403451525736225849 43203949802588644302169387)
          ·
            refine ⟨64805924703882966453254081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43203949802588644302169387 64805924703882966453254081)
            ·
              refine ⟨48604443527912224839940561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64805924703882966453254081 48604443527912224839940561)
              ·
                refine ⟨36453332645934168629955421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48604443527912224839940561 36453332645934168629955421)
                ·
                  refine ⟨13669999742225313236233283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36453332645934168629955421 13669999742225313236233283)
                  ·
                    refine ⟨20504999613337969854349925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13669999742225313236233283 20504999613337969854349925)
                    ·
                      refine ⟨3844687427500869347690611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20504999613337969854349925 3844687427500869347690611)
                      ·
                        rfl

theorem cell23_7487502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_7487502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487502 prefixEnd_7487502 := by exact prefixLift 7487502
  have htrace : WordTrace (prefixWord ++ tailWord_7487502) baseStart_7487502 baseEnd_7487502 := by
    simpa [prefixWord, tailWord_7487502, baseEnd_7487502] using wordTrace_append hprefix tailTrace_7487502
  have hstable : (prefixWord ++ tailWord_7487502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487502).length < 2 ^ (prefixWord ++ tailWord_7487502).sum := by decide
  have hdescent : baseEnd_7487502 < baseStart_7487502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487505 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 3]
def baseStart_7487505 : Nat := 118140960795 + 7487505 * 2 ^ 59
def prefixEnd_7487505 : Nat := 4983230072969 + 3 ^ 40 * 7487505 * 2
def baseEnd_7487505 : Nat := 3844688967942832835953097

theorem tailTrace_7487505 : CollatzResearch.WordTrace tailWord_7487505 prefixEnd_7487505 3844688967942832835953097 := by
  unfold tailWord_7487505
  simp only [CollatzResearch.WordTrace]
  refine ⟨273091742739055623891503969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182061161826037082594335979 273091742739055623891503969)
  ·
    refine ⟨204818807054291717918627977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273091742739055623891503969 204818807054291717918627977)
    ·
      refine ⟨153614105290718788438970983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204818807054291717918627977 153614105290718788438970983)
      ·
        refine ⟨230421157936078182658456475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153614105290718788438970983 230421157936078182658456475)
        ·
          refine ⟨345631736904117273987684713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230421157936078182658456475 345631736904117273987684713)
          ·
            refine ⟨259223802678087955490763535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345631736904117273987684713 259223802678087955490763535)
            ·
              refine ⟨388835704017131933236145303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259223802678087955490763535 388835704017131933236145303)
              ·
                refine ⟨583253556025697899854217955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388835704017131933236145303 583253556025697899854217955)
                ·
                  refine ⟨874880334038546849781326933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583253556025697899854217955 874880334038546849781326933)
                  ·
                    refine ⟨10252503914514220895874925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 874880334038546849781326933 10252503914514220895874925)
                    ·
                      refine ⟨3844688967942832835953097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10252503914514220895874925 3844688967942832835953097)
                      ·
                        rfl

theorem cell23_7487505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_7487505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487505 prefixEnd_7487505 := by exact prefixLift 7487505
  have htrace : WordTrace (prefixWord ++ tailWord_7487505) baseStart_7487505 baseEnd_7487505 := by
    simpa [prefixWord, tailWord_7487505, baseEnd_7487505] using wordTrace_append hprefix tailTrace_7487505
  have hstable : (prefixWord ++ tailWord_7487505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487505).length < 2 ^ (prefixWord ++ tailWord_7487505).sum := by decide
  have hdescent : baseEnd_7487505 < baseStart_7487505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487519 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 5, 2, 2]
def baseStart_7487519 : Nat := 118140960795 + 7487519 * 2 ^ 59
def prefixEnd_7487519 : Nat := 4983230072969 + 3 ^ 40 * 7487519 * 2
def baseEnd_7487519 : Nat := 3844696156671995781178033

theorem tailTrace_7487519 : CollatzResearch.WordTrace tailWord_7487519 prefixEnd_7487519 3844696156671995781178033 := by
  unfold tailWord_7487519
  simp only [CollatzResearch.WordTrace]
  refine ⟨273092253361004904282513611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182061502240669936188342407 273092253361004904282513611)
  ·
    refine ⟨409638380041507356423770417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273092253361004904282513611 409638380041507356423770417)
    ·
      refine ⟨307228785031130517317827813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409638380041507356423770417 307228785031130517317827813)
      ·
        refine ⟨57605397193336971997092715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307228785031130517317827813 57605397193336971997092715)
        ·
          refine ⟨86408095790005457995639073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57605397193336971997092715 86408095790005457995639073)
          ·
            refine ⟨64806071842504093496729305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86408095790005457995639073 64806071842504093496729305)
            ·
              refine ⟨48604553881878070122546979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64806071842504093496729305 48604553881878070122546979)
              ·
                refine ⟨72906830822817105183820469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48604553881878070122546979 72906830822817105183820469)
                ·
                  refine ⟨6835015389639103610983169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72906830822817105183820469 6835015389639103610983169)
                  ·
                    refine ⟨5126261542229327708237377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6835015389639103610983169 5126261542229327708237377)
                    ·
                      refine ⟨3844696156671995781178033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5126261542229327708237377 3844696156671995781178033)
                      ·
                        rfl

theorem cell23_7487519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_7487519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487519 prefixEnd_7487519 := by exact prefixLift 7487519
  have htrace : WordTrace (prefixWord ++ tailWord_7487519) baseStart_7487519 baseEnd_7487519 := by
    simpa [prefixWord, tailWord_7487519, baseEnd_7487519] using wordTrace_append hprefix tailTrace_7487519
  have hstable : (prefixWord ++ tailWord_7487519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487519).length < 2 ^ (prefixWord ++ tailWord_7487519).sum := by decide
  have hdescent : baseEnd_7487519 < baseStart_7487519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487525 : List Nat := [1, 3, 1, 2, 2, 3, 2, 9]
def baseStart_7487525 : Nat := 118140960795 + 7487525 * 2 ^ 59
def prefixEnd_7487525 : Nat := 4983230072969 + 3 ^ 40 * 7487525 * 2
def baseEnd_7487525 : Nat := 142396268057626768803815

theorem tailTrace_7487525 : CollatzResearch.WordTrace tailWord_7487525 prefixEnd_7487525 142396268057626768803815 := by
  unfold tailWord_7487525
  simp only [CollatzResearch.WordTrace]
  refine ⟨273092472198983167307232029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182061648132655444871488019 273092472198983167307232029)
  ·
    refine ⟨102409677074618687740212011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273092472198983167307232029 102409677074618687740212011)
    ·
      refine ⟨153614515611928031610318017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102409677074618687740212011 153614515611928031610318017)
      ·
        refine ⟨115210886708946023707738513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153614515611928031610318017 115210886708946023707738513)
        ·
          refine ⟨86408165031709517780803885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115210886708946023707738513 86408165031709517780803885)
          ·
            refine ⟨32403061886891069167801457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86408165031709517780803885 32403061886891069167801457)
            ·
              refine ⟨24302296415168301875851093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32403061886891069167801457 24302296415168301875851093)
              ·
                refine ⟨142396268057626768803815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24302296415168301875851093 142396268057626768803815)
                ·
                  rfl

theorem cell23_7487525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 9].length) (baseStart_7487525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487525 prefixEnd_7487525 := by exact prefixLift 7487525
  have htrace : WordTrace (prefixWord ++ tailWord_7487525) baseStart_7487525 baseEnd_7487525 := by
    simpa [prefixWord, tailWord_7487525, baseEnd_7487525] using wordTrace_append hprefix tailTrace_7487525
  have hstable : (prefixWord ++ tailWord_7487525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487525).length < 2 ^ (prefixWord ++ tailWord_7487525).sum := by decide
  have hdescent : baseEnd_7487525 < baseStart_7487525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487585 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 3, 8]
def baseStart_7487585 : Nat := 118140960795 + 7487585 * 2 ^ 59
def prefixEnd_7487585 : Nat := 4983230072969 + 3 ^ 40 * 7487585 * 2
def baseEnd_7487585 : Nat := 1281576682131730840984243

theorem tailTrace_7487585 : CollatzResearch.WordTrace tailWord_7487585 prefixEnd_7487585 1281576682131730840984243 := by
  unfold tailWord_7487585
  simp only [CollatzResearch.WordTrace]
  refine ⟨273094660578765797554416209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182063107052510531702944139 273094660578765797554416209)
  ·
    refine ⟨204820995434074348165812157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273094660578765797554416209 204820995434074348165812157)
    ·
      refine ⟨76807873287777880562179559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204820995434074348165812157 76807873287777880562179559)
      ·
        refine ⟨115211809931666820843269339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76807873287777880562179559 115211809931666820843269339)
        ·
          refine ⟨172817714897500231264904009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115211809931666820843269339 172817714897500231264904009)
          ·
            refine ⟨129613286173125173448678007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172817714897500231264904009 129613286173125173448678007)
            ·
              refine ⟨194419929259687760173017011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129613286173125173448678007 194419929259687760173017011)
              ·
                refine ⟨291629893889531640259525517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194419929259687760173017011 291629893889531640259525517)
                ·
                  refine ⟨109361210208574365097322069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291629893889531640259525517 109361210208574365097322069)
                  ·
                    refine ⟨1281576682131730840984243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109361210208574365097322069 1281576682131730840984243)
                    ·
                      rfl

theorem cell23_7487585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_7487585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487585 prefixEnd_7487585 := by exact prefixLift 7487585
  have htrace : WordTrace (prefixWord ++ tailWord_7487585) baseStart_7487585 baseEnd_7487585 := by
    simpa [prefixWord, tailWord_7487585, baseEnd_7487585] using wordTrace_append hprefix tailTrace_7487585
  have hstable : (prefixWord ++ tailWord_7487585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487585).length < 2 ^ (prefixWord ++ tailWord_7487585).sum := by decide
  have hdescent : baseEnd_7487585 < baseStart_7487585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487596 : List Nat := [2, 2, 1, 1, 3, 4, 1, 3, 1, 3, 2]
def baseStart_7487596 : Nat := 118140960795 + 7487596 * 2 ^ 59
def prefixEnd_7487596 : Nat := 4983230072969 + 3 ^ 40 * 7487596 * 2
def baseEnd_7487596 : Nat := 3844735694682391979915179

theorem tailTrace_7487596 : CollatzResearch.WordTrace tailWord_7487596 prefixEnd_7487596 3844735694682391979915179 := by
  unfold tailWord_7487596
  simp only [CollatzResearch.WordTrace]
  refine ⟨136547530890862973216533321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182063374521150630955377761 136547530890862973216533321)
  ·
    refine ⟨102410648168147229912399991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136547530890862973216533321 102410648168147229912399991)
    ·
      refine ⟨153615972252220844868599987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102410648168147229912399991 153615972252220844868599987)
      ·
        refine ⟨230423958378331267302899981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153615972252220844868599987 230423958378331267302899981)
        ·
          refine ⟨86408984391874225238587493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230423958378331267302899981 86408984391874225238587493)
          ·
            refine ⟨16201684573476417232235155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86408984391874225238587493 16201684573476417232235155)
            ·
              refine ⟨24302526860214625848352733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16201684573476417232235155 24302526860214625848352733)
              ·
                refine ⟨9113447572580484693132275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24302526860214625848352733 9113447572580484693132275)
                ·
                  refine ⟨13670171358870727039698413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9113447572580484693132275 13670171358870727039698413)
                  ·
                    refine ⟨5126314259576522639886905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13670171358870727039698413 5126314259576522639886905)
                    ·
                      refine ⟨3844735694682391979915179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5126314259576522639886905 3844735694682391979915179)
                      ·
                        rfl

theorem cell23_7487596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 3, 2].length) (baseStart_7487596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487596 prefixEnd_7487596 := by exact prefixLift 7487596
  have htrace : WordTrace (prefixWord ++ tailWord_7487596) baseStart_7487596 baseEnd_7487596 := by
    simpa [prefixWord, tailWord_7487596, baseEnd_7487596] using wordTrace_append hprefix tailTrace_7487596
  have hstable : (prefixWord ++ tailWord_7487596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487596).length < 2 ^ (prefixWord ++ tailWord_7487596).sum := by decide
  have hdescent : baseEnd_7487596 < baseStart_7487596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487602 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_7487602 : Nat := 118140960795 + 7487602 * 2 ^ 59
def prefixEnd_7487602 : Nat := 4983230072969 + 3 ^ 40 * 7487602 * 2
def baseEnd_7487602 : Nat := 1281579591855439652146717

theorem tailTrace_7487602 : CollatzResearch.WordTrace tailWord_7487602 prefixEnd_7487602 1281579591855439652146717 := by
  unfold tailWord_7487602
  simp only [CollatzResearch.WordTrace]
  refine ⟨68273820154926052364446265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182063520413136139638523373 68273820154926052364446265)
  ·
    refine ⟨51205365116194539273334699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68273820154926052364446265 51205365116194539273334699)
    ·
      refine ⟨76808047674291808910002049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51205365116194539273334699 76808047674291808910002049)
      ·
        refine ⟨57606035755718856682501537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76808047674291808910002049 57606035755718856682501537)
        ·
          refine ⟨43204526816789142511876153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57606035755718856682501537 43204526816789142511876153)
          ·
            refine ⟨32403395112591856883907115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43204526816789142511876153 32403395112591856883907115)
            ·
              refine ⟨48605092668887785325860673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32403395112591856883907115 48605092668887785325860673)
              ·
                refine ⟨36453819501665838994395505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48605092668887785325860673 36453819501665838994395505)
                ·
                  refine ⟨27340364626249379245796629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36453819501665838994395505 27340364626249379245796629)
                  ·
                    refine ⟨1281579591855439652146717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27340364626249379245796629 1281579591855439652146717)
                    ·
                      rfl

theorem cell23_7487602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_7487602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487602 prefixEnd_7487602 := by exact prefixLift 7487602
  have htrace : WordTrace (prefixWord ++ tailWord_7487602) baseStart_7487602 baseEnd_7487602 := by
    simpa [prefixWord, tailWord_7487602, baseEnd_7487602] using wordTrace_append hprefix tailTrace_7487602
  have hstable : (prefixWord ++ tailWord_7487602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487602).length < 2 ^ (prefixWord ++ tailWord_7487602).sum := by decide
  have hdescent : baseEnd_7487602 < baseStart_7487602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487626 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 1, 4, 2]
def baseStart_7487626 : Nat := 118140960795 + 7487626 * 2 ^ 59
def prefixEnd_7487626 : Nat := 4983230072969 + 3 ^ 40 * 7487626 * 2
def baseEnd_7487626 : Nat := 3844751099102026862540041

theorem tailTrace_7487626 : CollatzResearch.WordTrace tailWord_7487626 prefixEnd_7487626 3844751099102026862540041 := by
  unfold tailWord_7487626
  simp only [CollatzResearch.WordTrace]
  refine ⟨68274038992904315389164683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182064103981078174371105821 68274038992904315389164683)
  ·
    refine ⟨102411058489356473083747025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68274038992904315389164683 102411058489356473083747025)
    ·
      refine ⟨76808293867017354812810269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102411058489356473083747025 76808293867017354812810269)
      ·
        refine ⟨28803110200131508054803851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76808293867017354812810269 28803110200131508054803851)
        ·
          refine ⟨43204665300197262082205777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28803110200131508054803851 43204665300197262082205777)
          ·
            refine ⟨32403498975147946561654333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43204665300197262082205777 32403498975147946561654333)
            ·
              refine ⟨12151312115680479960620375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32403498975147946561654333 12151312115680479960620375)
              ·
                refine ⟨18226968173520719940930563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12151312115680479960620375 18226968173520719940930563)
                ·
                  refine ⟨27340452260281079911395845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18226968173520719940930563 27340452260281079911395845)
                  ·
                    refine ⟨5126334798802702483386721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27340452260281079911395845 5126334798802702483386721)
                    ·
                      refine ⟨3844751099102026862540041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5126334798802702483386721 3844751099102026862540041)
                      ·
                        rfl

theorem cell23_7487626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_7487626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487626 prefixEnd_7487626 := by exact prefixLift 7487626
  have htrace : WordTrace (prefixWord ++ tailWord_7487626) baseStart_7487626 baseEnd_7487626 := by
    simpa [prefixWord, tailWord_7487626, baseEnd_7487626] using wordTrace_append hprefix tailTrace_7487626
  have hstable : (prefixWord ++ tailWord_7487626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487626).length < 2 ^ (prefixWord ++ tailWord_7487626).sum := by decide
  have hdescent : baseEnd_7487626 < baseStart_7487626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487638 : List Nat := [5, 3, 2, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_7487638 : Nat := 118140960795 + 7487638 * 2 ^ 59
def prefixEnd_7487638 : Nat := 4983230072969 + 3 ^ 40 * 7487638 * 2
def baseEnd_7487638 : Nat := 3844757260869880815589987

theorem tailTrace_7487638 : CollatzResearch.WordTrace tailWord_7487638 prefixEnd_7487638 3844757260869880815589987 := by
  unfold tailWord_7487638
  simp only [CollatzResearch.WordTrace]
  refine ⟨17068537102973361725380973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182064395765049191737397045 17068537102973361725380973)
  ·
    refine ⟨6400701413615010647017865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17068537102973361725380973 6400701413615010647017865)
    ·
      refine ⟨4800526060211257985263399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6400701413615010647017865 4800526060211257985263399)
      ·
        refine ⟨7200789090316886977895099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4800526060211257985263399 7200789090316886977895099)
        ·
          refine ⟨10801183635475330466842649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7200789090316886977895099 10801183635475330466842649)
          ·
            refine ⟨8100887726606497850131987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10801183635475330466842649 8100887726606497850131987)
            ·
              refine ⟨12151331589909746775197981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8100887726606497850131987 12151331589909746775197981)
              ·
                refine ⟨4556749346216155040699243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12151331589909746775197981 4556749346216155040699243)
                ·
                  refine ⟨6835124019324232561048865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556749346216155040699243 6835124019324232561048865)
                  ·
                    refine ⟨5126343014493174420786649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6835124019324232561048865 5126343014493174420786649)
                    ·
                      refine ⟨3844757260869880815589987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5126343014493174420786649 3844757260869880815589987)
                      ·
                        rfl

theorem cell23_7487638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_7487638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487638 prefixEnd_7487638 := by exact prefixLift 7487638
  have htrace : WordTrace (prefixWord ++ tailWord_7487638) baseStart_7487638 baseEnd_7487638 := by
    simpa [prefixWord, tailWord_7487638, baseEnd_7487638] using wordTrace_append hprefix tailTrace_7487638
  have hstable : (prefixWord ++ tailWord_7487638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487638).length < 2 ^ (prefixWord ++ tailWord_7487638).sum := by decide
  have hdescent : baseEnd_7487638 < baseStart_7487638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487646 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_7487646 : Nat := 118140960795 + 7487646 * 2 ^ 59
def prefixEnd_7487646 : Nat := 4983230072969 + 3 ^ 40 * 7487646 * 2
def baseEnd_7487646 : Nat := 3844761368715116784289949

theorem tailTrace_7487646 : CollatzResearch.WordTrace tailWord_7487646 prefixEnd_7487646 3844761368715116784289949 := by
  unfold tailWord_7487646
  simp only [CollatzResearch.WordTrace]
  refine ⟨34137110678943100621548349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182064590287696536648257861 34137110678943100621548349)
  ·
    refine ⟨12801416504603662733080631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34137110678943100621548349 12801416504603662733080631)
    ·
      refine ⟨19202124756905494099620947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12801416504603662733080631 19202124756905494099620947)
      ·
        refine ⟨28803187135358241149431421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19202124756905494099620947 28803187135358241149431421)
        ·
          refine ⟨10801195175759340431036783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28803187135358241149431421 10801195175759340431036783)
          ·
            refine ⟨16201792763639010646555175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10801195175759340431036783 16201792763639010646555175)
            ·
              refine ⟨24302689145458515969832763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16201792763639010646555175 24302689145458515969832763)
              ·
                refine ⟨36454033718187773954749145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24302689145458515969832763 36454033718187773954749145)
                ·
                  refine ⟨27340525288640830466061859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36454033718187773954749145 27340525288640830466061859)
                  ·
                    refine ⟨41010787932961245699092789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27340525288640830466061859 41010787932961245699092789)
                    ·
                      refine ⟨3844761368715116784289949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41010787932961245699092789 3844761368715116784289949)
                      ·
                        rfl

theorem cell23_7487646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_7487646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487646 prefixEnd_7487646 := by exact prefixLift 7487646
  have htrace : WordTrace (prefixWord ++ tailWord_7487646) baseStart_7487646 baseEnd_7487646 := by
    simpa [prefixWord, tailWord_7487646, baseEnd_7487646] using wordTrace_append hprefix tailTrace_7487646
  have hstable : (prefixWord ++ tailWord_7487646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487646).length < 2 ^ (prefixWord ++ tailWord_7487646).sum := by decide
  have hdescent : baseEnd_7487646 < baseStart_7487646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487666 : List Nat := [3, 2, 1, 1, 1, 3, 5, 2, 5]
def baseStart_7487666 : Nat := 118140960795 + 7487666 * 2 ^ 59
def prefixEnd_7487666 : Nat := 4983230072969 + 3 ^ 40 * 7487666 * 2
def baseEnd_7487666 : Nat := 427196848703134078448873

theorem tailTrace_7487666 : CollatzResearch.WordTrace tailWord_7487666 prefixEnd_7487666 427196848703134078448873 := by
  unfold tailWord_7487666
  simp only [CollatzResearch.WordTrace]
  refine ⟨68274403722868087097028713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182065076594314898925409901 68274403722868087097028713)
  ·
    refine ⟨51205802792151065322771535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68274403722868087097028713 51205802792151065322771535)
    ·
      refine ⟨76808704188226597984157303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51205802792151065322771535 76808704188226597984157303)
      ·
        refine ⟨115213056282339896976235955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76808704188226597984157303 115213056282339896976235955)
        ·
          refine ⟨172819584423509845464353933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115213056282339896976235955 172819584423509845464353933)
          ·
            refine ⟨64807344158816192049132725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172819584423509845464353933 64807344158816192049132725)
            ·
              refine ⟨6075688514889018004606193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64807344158816192049132725 6075688514889018004606193)
              ·
                refine ⟨4556766386166763503454645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6075688514889018004606193 4556766386166763503454645)
                ·
                  refine ⟨427196848703134078448873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4556766386166763503454645 427196848703134078448873)
                  ·
                    rfl

theorem cell23_7487666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_7487666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487666 prefixEnd_7487666 := by exact prefixLift 7487666
  have htrace : WordTrace (prefixWord ++ tailWord_7487666) baseStart_7487666 baseEnd_7487666 := by
    simpa [prefixWord, tailWord_7487666, baseEnd_7487666] using wordTrace_append hprefix tailTrace_7487666
  have hstable : (prefixWord ++ tailWord_7487666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487666).length < 2 ^ (prefixWord ++ tailWord_7487666).sum := by decide
  have hdescent : baseEnd_7487666 < baseStart_7487666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487672 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_7487672 : Nat := 118140960795 + 7487672 * 2 ^ 59
def prefixEnd_7487672 : Nat := 4983230072969 + 3 ^ 40 * 7487672 * 2
def baseEnd_7487672 : Nat := 3844774719212133682564829

theorem tailTrace_7487672 : CollatzResearch.WordTrace tailWord_7487672 prefixEnd_7487672 3844774719212133682564829 := by
  unfold tailWord_7487672
  simp only [CollatzResearch.WordTrace]
  refine ⟨136548916864725305706416635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182065222486300407608555513 136548916864725305706416635)
  ·
    refine ⟨204823375297087958559624953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136548916864725305706416635 204823375297087958559624953)
    ·
      refine ⟨153617531472815968919718715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204823375297087958559624953 153617531472815968919718715)
      ·
        refine ⟨230426297209223953379578073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153617531472815968919718715 230426297209223953379578073)
        ·
          refine ⟨172819722906917965034683555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230426297209223953379578073 172819722906917965034683555)
          ·
            refine ⟨259229584360376947552025333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172819722906917965034683555 259229584360376947552025333)
            ·
              refine ⟨24302773533785338833002375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259229584360376947552025333 24302773533785338833002375)
              ·
                refine ⟨36454160300678008249503563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24302773533785338833002375 36454160300678008249503563)
                ·
                  refine ⟨54681240451017012374255345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36454160300678008249503563 54681240451017012374255345)
                  ·
                    refine ⟨41010930338262759280691509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54681240451017012374255345 41010930338262759280691509)
                    ·
                      refine ⟨3844774719212133682564829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41010930338262759280691509 3844774719212133682564829)
                      ·
                        rfl

theorem cell23_7487672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_7487672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487672 prefixEnd_7487672 := by exact prefixLift 7487672
  have htrace : WordTrace (prefixWord ++ tailWord_7487672) baseStart_7487672 baseEnd_7487672 := by
    simpa [prefixWord, tailWord_7487672, baseEnd_7487672] using wordTrace_append hprefix tailTrace_7487672
  have hstable : (prefixWord ++ tailWord_7487672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487672).length < 2 ^ (prefixWord ++ tailWord_7487672).sum := by decide
  have hdescent : baseEnd_7487672 < baseStart_7487672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487712 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 6]
def baseStart_7487712 : Nat := 118140960795 + 7487712 * 2 ^ 59
def prefixEnd_7487712 : Nat := 4983230072969 + 3 ^ 40 * 7487712 * 2
def baseEnd_7487712 : Nat := 3844795258438313526064645

theorem tailTrace_7487712 : CollatzResearch.WordTrace tailWord_7487712 prefixEnd_7487712 3844795258438313526064645 := by
  unfold tailWord_7487712
  simp only [CollatzResearch.WordTrace]
  refine ⟨136549646324652849122144695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182066195099537132162859593 136549646324652849122144695)
  ·
    refine ⟨204824469486979273683217043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136549646324652849122144695 204824469486979273683217043)
    ·
      refine ⟨307236704230468910524825565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204824469486979273683217043 307236704230468910524825565)
      ·
        refine ⟨115213764086425841446809587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307236704230468910524825565 115213764086425841446809587)
        ·
          refine ⟨172820646129638762170214381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115213764086425841446809587 172820646129638762170214381)
          ·
            refine ⟨64807742298614535813830393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172820646129638762170214381 64807742298614535813830393)
            ·
              refine ⟨48605806723960901860372795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64807742298614535813830393 48605806723960901860372795)
              ·
                refine ⟨72908710085941352790559193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48605806723960901860372795 72908710085941352790559193)
                ·
                  refine ⟨54681532564456014592919395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72908710085941352790559193 54681532564456014592919395)
                  ·
                    refine ⟨82022298846684021889379093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54681532564456014592919395 82022298846684021889379093)
                    ·
                      refine ⟨3844795258438313526064645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82022298846684021889379093 3844795258438313526064645)
                      ·
                        rfl

theorem cell23_7487712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_7487712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487712 prefixEnd_7487712 := by exact prefixLift 7487712
  have htrace : WordTrace (prefixWord ++ tailWord_7487712) baseStart_7487712 baseEnd_7487712 := by
    simpa [prefixWord, tailWord_7487712, baseEnd_7487712] using wordTrace_append hprefix tailTrace_7487712
  have hstable : (prefixWord ++ tailWord_7487712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487712).length < 2 ^ (prefixWord ++ tailWord_7487712).sum := by decide
  have hdescent : baseEnd_7487712 < baseStart_7487712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487773 : List Nat := [1, 4, 2, 3, 2, 2, 1, 2, 6]
def baseStart_7487773 : Nat := 118140960795 + 7487773 * 2 ^ 59
def prefixEnd_7487773 : Nat := 4983230072969 + 3 ^ 40 * 7487773 * 2
def baseEnd_7487773 : Nat := 427202953417581976377985

theorem tailTrace_7487773 : CollatzResearch.WordTrace tailWord_7487773 prefixEnd_7487773 427202953417581976377985 := by
  unfold tailWord_7487773
  simp only [CollatzResearch.WordTrace]
  refine ⟨273101517502084705662259973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182067678334723137108173315 273101517502084705662259973)
  ·
    refine ⟨51206534531640882311673745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273101517502084705662259973 51206534531640882311673745)
    ·
      refine ⟨38404900898730661733755309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51206534531640882311673745 38404900898730661733755309)
      ·
        refine ⟨14401837837023998150158241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38404900898730661733755309 14401837837023998150158241)
        ·
          refine ⟨10801378377767998612618681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14401837837023998150158241 10801378377767998612618681)
          ·
            refine ⟨8101033783325998959464011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10801378377767998612618681 8101033783325998959464011)
            ·
              refine ⟨12151550674988998439196017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8101033783325998959464011 12151550674988998439196017)
              ·
                refine ⟨9113663006241748829397013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12151550674988998439196017 9113663006241748829397013)
                ·
                  refine ⟨427202953417581976377985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9113663006241748829397013 427202953417581976377985)
                  ·
                    rfl

theorem cell23_7487773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_7487773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487773 prefixEnd_7487773 := by exact prefixLift 7487773
  have htrace : WordTrace (prefixWord ++ tailWord_7487773) baseStart_7487773 baseEnd_7487773 := by
    simpa [prefixWord, tailWord_7487773, baseEnd_7487773] using wordTrace_append hprefix tailTrace_7487773
  have hstable : (prefixWord ++ tailWord_7487773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487773).length < 2 ^ (prefixWord ++ tailWord_7487773).sum := by decide
  have hdescent : baseEnd_7487773 < baseStart_7487773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487790 : List Nat := [4, 1, 3, 3, 1, 1, 3, 1, 6]
def baseStart_7487790 : Nat := 118140960795 + 7487790 * 2 ^ 59
def prefixEnd_7487790 : Nat := 4983230072969 + 3 ^ 40 * 7487790 * 2
def baseEnd_7487790 : Nat := 427203923325484913432143

theorem tailTrace_7487790 : CollatzResearch.WordTrace tailWord_7487790 prefixEnd_7487790 427203923325484913432143 := by
  unfold tailWord_7487790
  simp only [CollatzResearch.WordTrace]
  refine ⟨34137767192877889695703603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182068091695348745043752549 34137767192877889695703603)
  ·
    refine ⟨51206650789316834543555405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34137767192877889695703603 51206650789316834543555405)
    ·
      refine ⟨19202494045993812953833277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51206650789316834543555405 19202494045993812953833277)
      ·
        refine ⟨7200935267247679857687479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19202494045993812953833277 7200935267247679857687479)
        ·
          refine ⟨10801402900871519786531219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7200935267247679857687479 10801402900871519786531219)
          ·
            refine ⟨16202104351307279679796829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10801402900871519786531219 16202104351307279679796829)
            ·
              refine ⟨6075789131740229879923811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16202104351307279679796829 6075789131740229879923811)
              ·
                refine ⟨9113683697610344819885717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6075789131740229879923811 9113683697610344819885717)
                ·
                  refine ⟨427203923325484913432143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9113683697610344819885717 427203923325484913432143)
                  ·
                    rfl

theorem cell23_7487790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_7487790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487790 prefixEnd_7487790 := by exact prefixLift 7487790
  have htrace : WordTrace (prefixWord ++ tailWord_7487790) baseStart_7487790 baseEnd_7487790 := by
    simpa [prefixWord, tailWord_7487790, baseEnd_7487790] using wordTrace_append hprefix tailTrace_7487790
  have hstable : (prefixWord ++ tailWord_7487790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487790).length < 2 ^ (prefixWord ++ tailWord_7487790).sum := by decide
  have hdescent : baseEnd_7487790 < baseStart_7487790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487850 : List Nat := [3, 1, 3, 3, 1, 1, 4, 1, 2, 4]
def baseStart_7487850 : Nat := 118140960795 + 7487850 * 2 ^ 59
def prefixEnd_7487850 : Nat := 4983230072969 + 3 ^ 40 * 7487850 * 2
def baseEnd_7487850 : Nat := 1281622039589544662046337

theorem tailTrace_7487850 : CollatzResearch.WordTrace tailWord_7487850 prefixEnd_7487850 1281622039589544662046337 := by
  unfold tailWord_7487850
  simp only [CollatzResearch.WordTrace]
  refine ⟨68276081480701436953203251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182069550615203831875208669 68276081480701436953203251)
  ·
    refine ⟨102414122221052155429804877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68276081480701436953203251 102414122221052155429804877)
    ·
      refine ⟨38405295832894558286176829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102414122221052155429804877 38405295832894558286176829)
      ·
        refine ⟨14401985937335459357316311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38405295832894558286176829 14401985937335459357316311)
        ·
          refine ⟨21602978906003189035974467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14401985937335459357316311 21602978906003189035974467)
          ·
            refine ⟨32404468359004783553961701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21602978906003189035974467 32404468359004783553961701)
            ·
              refine ⟨6075837817313396916367819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32404468359004783553961701 6075837817313396916367819)
              ·
                refine ⟨9113756725970095374551729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6075837817313396916367819 9113756725970095374551729)
                ·
                  refine ⟨6835317544477571530913797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9113756725970095374551729 6835317544477571530913797)
                  ·
                    refine ⟨1281622039589544662046337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6835317544477571530913797 1281622039589544662046337)
                    ·
                      rfl

theorem cell23_7487850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_7487850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487850 prefixEnd_7487850 := by exact prefixLift 7487850
  have htrace : WordTrace (prefixWord ++ tailWord_7487850) baseStart_7487850 baseEnd_7487850 := by
    simpa [prefixWord, tailWord_7487850, baseEnd_7487850] using wordTrace_append hprefix tailTrace_7487850
  have hstable : (prefixWord ++ tailWord_7487850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487850).length < 2 ^ (prefixWord ++ tailWord_7487850).sum := by decide
  have hdescent : baseEnd_7487850 < baseStart_7487850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487873 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_7487873 : Nat := 118140960795 + 7487873 * 2 ^ 59
def prefixEnd_7487873 : Nat := 4983230072969 + 3 ^ 40 * 7487873 * 2
def baseEnd_7487873 : Nat := 3844877928823687396151405

theorem tailTrace_7487873 : CollatzResearch.WordTrace tailWord_7487873 prefixEnd_7487873 3844877928823687396151405 := by
  unfold tailWord_7487873
  simp only [CollatzResearch.WordTrace]
  refine ⟨273105164801722422740900273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182070109867814948493933515 273105164801722422740900273)
  ·
    refine ⟨204828873601291817055675205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273105164801722422740900273 204828873601291817055675205)
    ·
      refine ⟨38405413800242215697939101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204828873601291817055675205 38405413800242215697939101)
      ·
        refine ⟨14402030175090830886727163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38405413800242215697939101 14402030175090830886727163)
        ·
          refine ⟨21603045262636246330090745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14402030175090830886727163 21603045262636246330090745)
          ·
            refine ⟨16202283946977184747568059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21603045262636246330090745 16202283946977184747568059)
            ·
              refine ⟨24303425920465777121352089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16202283946977184747568059 24303425920465777121352089)
              ·
                refine ⟨18227569440349332841014067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24303425920465777121352089 18227569440349332841014067)
                ·
                  refine ⟨27341354160523999261521101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18227569440349332841014067 27341354160523999261521101)
                  ·
                    refine ⟨10253007810196499723070413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27341354160523999261521101 10253007810196499723070413)
                    ·
                      refine ⟨3844877928823687396151405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10253007810196499723070413 3844877928823687396151405)
                      ·
                        rfl

theorem cell23_7487873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_7487873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487873 prefixEnd_7487873 := by exact prefixLift 7487873
  have htrace : WordTrace (prefixWord ++ tailWord_7487873) baseStart_7487873 baseEnd_7487873 := by
    simpa [prefixWord, tailWord_7487873, baseEnd_7487873] using wordTrace_append hprefix tailTrace_7487873
  have hstable : (prefixWord ++ tailWord_7487873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487873).length < 2 ^ (prefixWord ++ tailWord_7487873).sum := by decide
  have hdescent : baseEnd_7487873 < baseStart_7487873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487896 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 2, 3, 4]
def baseStart_7487896 : Nat := 118140960795 + 7487896 * 2 ^ 59
def prefixEnd_7487896 : Nat := 4983230072969 + 3 ^ 40 * 7487896 * 2
def baseEnd_7487896 : Nat := 3844889738878740806163799

theorem tailTrace_7487896 : CollatzResearch.WordTrace tailWord_7487896 prefixEnd_7487896 3844889738878740806163799 := by
  unfold tailWord_7487896
  simp only [CollatzResearch.WordTrace]
  refine ⟨136553001840319548834493771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182070669120426065112658361 136553001840319548834493771)
  ·
    refine ⟨204829502760479323251740657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136553001840319548834493771 204829502760479323251740657)
    ·
      refine ⟨153622127070359492438805493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204829502760479323251740657 153622127070359492438805493)
      ·
        refine ⟨14402074412846202416138015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153622127070359492438805493 14402074412846202416138015)
        ·
          refine ⟨21603111619269303624207023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14402074412846202416138015 21603111619269303624207023)
          ·
            refine ⟨32404667428903955436310535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21603111619269303624207023 32404667428903955436310535)
            ·
              refine ⟨48607001143355933154465803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32404667428903955436310535 48607001143355933154465803)
              ·
                refine ⟨72910501715033899731698705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48607001143355933154465803 72910501715033899731698705)
                ·
                  refine ⟨54682876286275424798774029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72910501715033899731698705 54682876286275424798774029)
                  ·
                    refine ⟨20506078607353284299540261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54682876286275424798774029 20506078607353284299540261)
                    ·
                      refine ⟨3844889738878740806163799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20506078607353284299540261 3844889738878740806163799)
                      ·
                        rfl

theorem cell23_7487896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_7487896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487896 prefixEnd_7487896 := by exact prefixLift 7487896
  have htrace : WordTrace (prefixWord ++ tailWord_7487896) baseStart_7487896 baseEnd_7487896 := by
    simpa [prefixWord, tailWord_7487896, baseEnd_7487896] using wordTrace_append hprefix tailTrace_7487896
  have hstable : (prefixWord ++ tailWord_7487896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487896).length < 2 ^ (prefixWord ++ tailWord_7487896).sum := by decide
  have hdescent : baseEnd_7487896 < baseStart_7487896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487906 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_7487906 : Nat := 118140960795 + 7487906 * 2 ^ 59
def prefixEnd_7487906 : Nat := 4983230072969 + 3 ^ 40 * 7487906 * 2
def baseEnd_7487906 : Nat := 1281631624561761922346251

theorem tailTrace_7487906 : CollatzResearch.WordTrace tailWord_7487906 prefixEnd_7487906 1281631624561761922346251 := by
  unfold tailWord_7487906
  simp only [CollatzResearch.WordTrace]
  refine ⟨68276592102650717344212893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182070912273735246251234381 68276592102650717344212893)
  ·
    refine ⟨25603722038494019004079835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68276592102650717344212893 25603722038494019004079835)
    ·
      refine ⟨38405583057741028506119753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25603722038494019004079835 38405583057741028506119753)
      ·
        refine ⟨28804187293305771379589815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38405583057741028506119753 28804187293305771379589815)
        ·
          refine ⟨43206280939958657069384723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28804187293305771379589815 43206280939958657069384723)
          ·
            refine ⟨64809421409937985604077085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43206280939958657069384723 64809421409937985604077085)
            ·
              refine ⟨24303533028726744601528907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64809421409937985604077085 24303533028726744601528907)
              ·
                refine ⟨36455299543090116902293361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24303533028726744601528907 36455299543090116902293361)
                ·
                  refine ⟨27341474657317587676720021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36455299543090116902293361 27341474657317587676720021)
                  ·
                    refine ⟨1281631624561761922346251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27341474657317587676720021 1281631624561761922346251)
                    ·
                      rfl

theorem cell23_7487906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_7487906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487906 prefixEnd_7487906 := by exact prefixLift 7487906
  have htrace : WordTrace (prefixWord ++ tailWord_7487906) baseStart_7487906 baseEnd_7487906 := by
    simpa [prefixWord, tailWord_7487906, baseEnd_7487906] using wordTrace_append hprefix tailTrace_7487906
  have hstable : (prefixWord ++ tailWord_7487906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487906).length < 2 ^ (prefixWord ++ tailWord_7487906).sum := by decide
  have hdescent : baseEnd_7487906 < baseStart_7487906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487946 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_7487946 : Nat := 118140960795 + 7487946 * 2 ^ 59
def prefixEnd_7487946 : Nat := 4983230072969 + 3 ^ 40 * 7487946 * 2
def baseEnd_7487946 : Nat := 3844915412911465610538569

theorem tailTrace_7487946 : CollatzResearch.WordTrace tailWord_7487946 prefixEnd_7487946 3844915412911465610538569 := by
  unfold tailWord_7487946
  simp only [CollatzResearch.WordTrace]
  refine ⟨68276956832614489052076923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182071884886971970805538461 68276956832614489052076923)
  ·
    refine ⟨102415435248921733578115385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68276956832614489052076923 102415435248921733578115385)
    ·
      refine ⟨76811576436691300183586539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102415435248921733578115385 76811576436691300183586539)
      ·
        refine ⟨115217364655036950275379809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76811576436691300183586539 115217364655036950275379809)
        ·
          refine ⟨86413023491277712706534857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115217364655036950275379809 86413023491277712706534857)
          ·
            refine ⟨64809767618458284529901143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86413023491277712706534857 64809767618458284529901143)
            ·
              refine ⟨97214651427687426794851715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64809767618458284529901143 97214651427687426794851715)
              ·
                refine ⟨145821977141531140192277573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97214651427687426794851715 145821977141531140192277573)
                ·
                  refine ⟨27341620714037088786052045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145821977141531140192277573 27341620714037088786052045)
                  ·
                    refine ⟨10253107767763908294769517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27341620714037088786052045 10253107767763908294769517)
                    ·
                      refine ⟨3844915412911465610538569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10253107767763908294769517 3844915412911465610538569)
                      ·
                        rfl

theorem cell23_7487946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_7487946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487946 prefixEnd_7487946 := by exact prefixLift 7487946
  have htrace : WordTrace (prefixWord ++ tailWord_7487946) baseStart_7487946 baseEnd_7487946 := by
    simpa [prefixWord, tailWord_7487946, baseEnd_7487946] using wordTrace_append hprefix tailTrace_7487946
  have hstable : (prefixWord ++ tailWord_7487946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487946).length < 2 ^ (prefixWord ++ tailWord_7487946).sum := by decide
  have hdescent : baseEnd_7487946 < baseStart_7487946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487979 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 2, 8]
def baseStart_7487979 : Nat := 118140960795 + 7487979 * 2 ^ 59
def prefixEnd_7487979 : Nat := 4983230072969 + 3 ^ 40 * 7487979 * 2
def baseEnd_7487979 : Nat := 1281644119257687993808639

theorem tailTrace_7487979 : CollatzResearch.WordTrace tailWord_7487979 prefixEnd_7487979 1281644119257687993808639 := by
  unfold tailWord_7487979
  simp only [CollatzResearch.WordTrace]
  refine ⟨273109030939338402844258991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182072687292892268562839327 273109030939338402844258991)
  ·
    refine ⟨409663546409007604266388487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273109030939338402844258991 409663546409007604266388487)
    ·
      refine ⟨614495319613511406399582731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409663546409007604266388487 614495319613511406399582731)
      ·
        refine ⟨921742979420267109599374097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614495319613511406399582731 921742979420267109599374097)
        ·
          refine ⟨691307234565200332199530573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921742979420267109599374097 691307234565200332199530573)
          ·
            refine ⟨259240212961950124574823965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 691307234565200332199530573 259240212961950124574823965)
            ·
              refine ⟨97215079860731296715558987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259240212961950124574823965 97215079860731296715558987)
              ·
                refine ⟨145822619791096945073338481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97215079860731296715558987 145822619791096945073338481)
                ·
                  refine ⟨109366964843322708805003861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145822619791096945073338481 109366964843322708805003861)
                  ·
                    refine ⟨1281644119257687993808639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109366964843322708805003861 1281644119257687993808639)
                    ·
                      rfl

theorem cell23_7487979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 8].length) (baseStart_7487979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7487979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7487979 prefixEnd_7487979 := by exact prefixLift 7487979
  have htrace : WordTrace (prefixWord ++ tailWord_7487979) baseStart_7487979 baseEnd_7487979 := by
    simpa [prefixWord, tailWord_7487979, baseEnd_7487979] using wordTrace_append hprefix tailTrace_7487979
  have hstable : (prefixWord ++ tailWord_7487979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487979).length < 2 ^ (prefixWord ++ tailWord_7487979).sum := by decide
  have hdescent : baseEnd_7487979 < baseStart_7487979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488040 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_7488040 : Nat := 118140960795 + 7488040 * 2 ^ 59
def prefixEnd_7488040 : Nat := 4983230072969 + 3 ^ 40 * 7488040 * 2
def baseEnd_7488040 : Nat := 3844963680092988242763137

theorem tailTrace_7488040 : CollatzResearch.WordTrace tailWord_7488040 prefixEnd_7488040 3844963680092988242763137 := by
  unfold tailWord_7488040
  simp only [CollatzResearch.WordTrace]
  refine ⟨136555627896058705131114787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182074170528078273508153049 136555627896058705131114787)
  ·
    refine ⟨204833441844088057696672181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136555627896058705131114787 204833441844088057696672181)
    ·
      refine ⟨19203135172883255409063017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204833441844088057696672181 19203135172883255409063017)
      ·
        refine ⟨14402351379662441556797263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19203135172883255409063017 14402351379662441556797263)
        ·
          refine ⟨21603527069493662335195895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14402351379662441556797263 21603527069493662335195895)
          ·
            refine ⟨32405290604240493502793843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21603527069493662335195895 32405290604240493502793843)
            ·
              refine ⟨48607935906360740254190765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32405290604240493502793843 48607935906360740254190765)
              ·
                refine ⟨18227975964885277595321537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48607935906360740254190765 18227975964885277595321537)
                ·
                  refine ⟨13670981973663958196491153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18227975964885277595321537 13670981973663958196491153)
                  ·
                    refine ⟨10253236480247968647368365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13670981973663958196491153 10253236480247968647368365)
                    ·
                      refine ⟨3844963680092988242763137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10253236480247968647368365 3844963680092988242763137)
                      ·
                        rfl

theorem cell23_7488040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_7488040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488040 prefixEnd_7488040 := by exact prefixLift 7488040
  have htrace : WordTrace (prefixWord ++ tailWord_7488040) baseStart_7488040 baseEnd_7488040 := by
    simpa [prefixWord, tailWord_7488040, baseEnd_7488040] using wordTrace_append hprefix tailTrace_7488040
  have hstable : (prefixWord ++ tailWord_7488040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488040).length < 2 ^ (prefixWord ++ tailWord_7488040).sum := by decide
  have hdescent : baseEnd_7488040 < baseStart_7488040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488097 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 2, 3, 2]
def baseStart_7488097 : Nat := 118140960795 + 7488097 * 2 ^ 59
def prefixEnd_7488097 : Nat := 4983230072969 + 3 ^ 40 * 7488097 * 2
def baseEnd_7488097 : Nat := 3844992948490294519750375

theorem tailTrace_7488097 : CollatzResearch.WordTrace tailWord_7488097 prefixEnd_7488097 3844992948490294519750375 := by
  unfold tailWord_7488097
  simp only [CollatzResearch.WordTrace]
  refine ⟨273113334752910908997054545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182075556501940605998036363 273113334752910908997054545)
  ·
    refine ⟨204835001064683181747790909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273113334752910908997054545 204835001064683181747790909)
    ·
      refine ⟨76813125399256193155421591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204835001064683181747790909 76813125399256193155421591)
      ·
        refine ⟨115219688098884289733132387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76813125399256193155421591 115219688098884289733132387)
        ·
          refine ⟨172829532148326434599698581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115219688098884289733132387 172829532148326434599698581)
          ·
            refine ⟨8101384319452801621860871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172829532148326434599698581 8101384319452801621860871)
            ·
              refine ⟨12152076479179202432791307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8101384319452801621860871 12152076479179202432791307)
              ·
                refine ⟨18228114718768803649186961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12152076479179202432791307 18228114718768803649186961)
                ·
                  refine ⟨13671086039076602736890221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18228114718768803649186961 13671086039076602736890221)
                  ·
                    refine ⟨5126657264653726026333833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13671086039076602736890221 5126657264653726026333833)
                    ·
                      refine ⟨3844992948490294519750375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5126657264653726026333833 3844992948490294519750375)
                      ·
                        rfl

theorem cell23_7488097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_7488097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488097 prefixEnd_7488097 := by exact prefixLift 7488097
  have htrace : WordTrace (prefixWord ++ tailWord_7488097) baseStart_7488097 baseEnd_7488097 := by
    simpa [prefixWord, tailWord_7488097, baseEnd_7488097] using wordTrace_append hprefix tailTrace_7488097
  have hstable : (prefixWord ++ tailWord_7488097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488097).length < 2 ^ (prefixWord ++ tailWord_7488097).sum := by decide
  have hdescent : baseEnd_7488097 < baseStart_7488097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488103 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 4, 4]
def baseStart_7488103 : Nat := 118140960795 + 7488103 * 2 ^ 59
def prefixEnd_7488103 : Nat := 4983230072969 + 3 ^ 40 * 7488103 * 2
def baseEnd_7488103 : Nat := 1281665343124740498758449

theorem tailTrace_7488103 : CollatzResearch.WordTrace tailWord_7488103 prefixEnd_7488103 1281665343124740498758449 := by
  unfold tailWord_7488103
  simp only [CollatzResearch.WordTrace]
  refine ⟨273113553590889172021772963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182075702393926114681181975 273113553590889172021772963)
  ·
    refine ⟨409670330386333758032659445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273113553590889172021772963 409670330386333758032659445)
    ·
      refine ⟨38406593473718789815561823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 409670330386333758032659445 38406593473718789815561823)
      ·
        refine ⟨57609890210578184723342735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38406593473718789815561823 57609890210578184723342735)
        ·
          refine ⟨86414835315867277085014103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57609890210578184723342735 86414835315867277085014103)
          ·
            refine ⟨129622252973800915627521155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86414835315867277085014103 129622252973800915627521155)
            ·
              refine ⟨194433379460701373441281733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129622252973800915627521155 194433379460701373441281733)
              ·
                refine ⟨36456258648881507520240325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194433379460701373441281733 36456258648881507520240325)
                ·
                  refine ⟨6835548496665282660045061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36456258648881507520240325 6835548496665282660045061)
                  ·
                    refine ⟨1281665343124740498758449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6835548496665282660045061 1281665343124740498758449)
                    ·
                      rfl

theorem cell23_7488103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_7488103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488103 prefixEnd_7488103 := by exact prefixLift 7488103
  have htrace : WordTrace (prefixWord ++ tailWord_7488103) baseStart_7488103 baseEnd_7488103 := by
    simpa [prefixWord, tailWord_7488103, baseEnd_7488103] using wordTrace_append hprefix tailTrace_7488103
  have hstable : (prefixWord ++ tailWord_7488103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488103).length < 2 ^ (prefixWord ++ tailWord_7488103).sum := by decide
  have hdescent : baseEnd_7488103 < baseStart_7488103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488167 : List Nat := [1, 1, 6, 3, 2, 1, 9]
def baseStart_7488167 : Nat := 118140960795 + 7488167 * 2 ^ 59
def prefixEnd_7488167 : Nat := 4983230072969 + 3 ^ 40 * 7488167 * 2
def baseEnd_7488167 : Nat := 47469492495507521554013

theorem tailTrace_7488167 : CollatzResearch.WordTrace tailWord_7488167 prefixEnd_7488167 47469492495507521554013 := by
  unfold tailWord_7488167
  simp only [CollatzResearch.WordTrace]
  refine ⟨273115887862657310952102755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182077258575104873968068503 273115887862657310952102755)
  ·
    refine ⟨409673831793985966428154133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273115887862657310952102755 409673831793985966428154133)
    ·
      refine ⟨19203460865343092176319725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 409673831793985966428154133 19203460865343092176319725)
      ·
        refine ⟨7201297824503659566119897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19203460865343092176319725 7201297824503659566119897)
        ·
          refine ⟨5400973368377744674589923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7201297824503659566119897 5400973368377744674589923)
          ·
            refine ⟨8101460052566617011884885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5400973368377744674589923 8101460052566617011884885)
            ·
              refine ⟨47469492495507521554013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8101460052566617011884885 47469492495507521554013)
              ·
                rfl

theorem cell23_7488167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 9].length) (baseStart_7488167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488167 prefixEnd_7488167 := by exact prefixLift 7488167
  have htrace : WordTrace (prefixWord ++ tailWord_7488167) baseStart_7488167 baseEnd_7488167 := by
    simpa [prefixWord, tailWord_7488167, baseEnd_7488167] using wordTrace_append hprefix tailTrace_7488167
  have hstable : (prefixWord ++ tailWord_7488167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488167).length < 2 ^ (prefixWord ++ tailWord_7488167).sum := by decide
  have hdescent : baseEnd_7488167 < baseStart_7488167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488198 : List Nat := [6, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_7488198 : Nat := 118140960795 + 7488198 * 2 ^ 59
def prefixEnd_7488198 : Nat := 4983230072969 + 3 ^ 40 * 7488198 * 2
def baseEnd_7488198 : Nat := 3845044810036398624587411

theorem tailTrace_7488198 : CollatzResearch.WordTrace tailWord_7488198 prefixEnd_7488198 3845044810036398624587411 := by
  unfold tailWord_7488198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8534906828923281351452539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182078012350363335497654165 8534906828923281351452539)
  ·
    refine ⟨12802360243384922027178809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8534906828923281351452539 12802360243384922027178809)
    ·
      refine ⟨9601770182538691520384107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12802360243384922027178809 9601770182538691520384107)
      ·
        refine ⟨14402655273808037280576161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9601770182538691520384107 14402655273808037280576161)
        ·
          refine ⟨10801991455356027960432121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14402655273808037280576161 10801991455356027960432121)
          ·
            refine ⟨8101493591517020970324091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10801991455356027960432121 8101493591517020970324091)
            ·
              refine ⟨12152240387275531455486137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8101493591517020970324091 12152240387275531455486137)
              ·
                refine ⟨9114180290456648591614603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12152240387275531455486137 9114180290456648591614603)
                ·
                  refine ⟨13671270435684972887421905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9114180290456648591614603 13671270435684972887421905)
                  ·
                    refine ⟨10253452826763729665566429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13671270435684972887421905 10253452826763729665566429)
                    ·
                      refine ⟨3845044810036398624587411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10253452826763729665566429 3845044810036398624587411)
                      ·
                        rfl

theorem cell23_7488198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_7488198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488198 prefixEnd_7488198 := by exact prefixLift 7488198
  have htrace : WordTrace (prefixWord ++ tailWord_7488198) baseStart_7488198 baseEnd_7488198 := by
    simpa [prefixWord, tailWord_7488198, baseEnd_7488198] using wordTrace_append hprefix tailTrace_7488198
  have hstable : (prefixWord ++ tailWord_7488198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488198).length < 2 ^ (prefixWord ++ tailWord_7488198).sum := by decide
  have hdescent : baseEnd_7488198 < baseStart_7488198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488204 : List Nat := [2, 2, 1, 5, 1, 1, 3, 2, 1, 3, 2]
def baseStart_7488204 : Nat := 118140960795 + 7488204 * 2 ^ 59
def prefixEnd_7488204 : Nat := 4983230072969 + 3 ^ 40 * 7488204 * 2
def baseEnd_7488204 : Nat := 3845047890920325601112383

theorem tailTrace_7488204 : CollatzResearch.WordTrace tailWord_7488204 prefixEnd_7488204 3845047890920325601112383 := by
  unfold tailWord_7488204
  simp only [CollatzResearch.WordTrace]
  refine ⟨136558618681761633135599833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182078158242348844180799777 136558618681761633135599833)
  ·
    refine ⟨102418964011321224851699875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136558618681761633135599833 102418964011321224851699875)
    ·
      refine ⟨153628446016981837277549813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102418964011321224851699875 153628446016981837277549813)
      ·
        refine ⟨14402666814092047244770295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153628446016981837277549813 14402666814092047244770295)
        ·
          refine ⟨21604000221138070867155443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14402666814092047244770295 21604000221138070867155443)
          ·
            refine ⟨32406000331707106300733165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21604000221138070867155443 32406000331707106300733165)
            ·
              refine ⟨12152250124390164862774937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32406000331707106300733165 12152250124390164862774937)
              ·
                refine ⟨9114187593292623647081203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12152250124390164862774937 9114187593292623647081203)
                ·
                  refine ⟨13671281389938935470621805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9114187593292623647081203 13671281389938935470621805)
                  ·
                    refine ⟨5126730521227100801483177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13671281389938935470621805 5126730521227100801483177)
                    ·
                      refine ⟨3845047890920325601112383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5126730521227100801483177 3845047890920325601112383)
                      ·
                        rfl

theorem cell23_7488204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_7488204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488204 prefixEnd_7488204 := by exact prefixLift 7488204
  have htrace : WordTrace (prefixWord ++ tailWord_7488204) baseStart_7488204 baseEnd_7488204 := by
    simpa [prefixWord, tailWord_7488204, baseEnd_7488204] using wordTrace_append hprefix tailTrace_7488204
  have hstable : (prefixWord ++ tailWord_7488204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488204).length < 2 ^ (prefixWord ++ tailWord_7488204).sum := by decide
  have hdescent : baseEnd_7488204 < baseStart_7488204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488240 : List Nat := [2, 1, 1, 1, 3, 1, 5, 4, 5]
def baseStart_7488240 : Nat := 118140960795 + 7488240 * 2 ^ 59
def prefixEnd_7488240 : Nat := 4983230072969 + 3 ^ 40 * 7488240 * 2
def baseEnd_7488240 : Nat := 427229597358209717806913

theorem tailTrace_7488240 : CollatzResearch.WordTrace tailWord_7488240 prefixEnd_7488240 427229597358209717806913 := by
  unfold tailWord_7488240
  simp only [CollatzResearch.WordTrace]
  refine ⟨136559275195696422209755087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182079033594261896279673449 136559275195696422209755087)
  ·
    refine ⟨204838912793544633314632631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136559275195696422209755087 204838912793544633314632631)
    ·
      refine ⟨307258369190316949971948947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204838912793544633314632631 307258369190316949971948947)
      ·
        refine ⟨460887553785475424957923421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307258369190316949971948947 460887553785475424957923421)
        ·
          refine ⟨172832832669553284359221283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460887553785475424957923421 172832832669553284359221283)
          ·
            refine ⟨259249249004329926538831925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172832832669553284359221283 259249249004329926538831925)
            ·
              refine ⟨24304617094155930613015493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259249249004329926538831925 24304617094155930613015493)
              ·
                refine ⟨4557115705154236989940405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24304617094155930613015493 4557115705154236989940405)
                ·
                  refine ⟨427229597358209717806913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4557115705154236989940405 427229597358209717806913)
                  ·
                    rfl

theorem cell23_7488240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 5].length) (baseStart_7488240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488240 prefixEnd_7488240 := by exact prefixLift 7488240
  have htrace : WordTrace (prefixWord ++ tailWord_7488240) baseStart_7488240 baseEnd_7488240 := by
    simpa [prefixWord, tailWord_7488240, baseEnd_7488240] using wordTrace_append hprefix tailTrace_7488240
  have hstable : (prefixWord ++ tailWord_7488240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488240).length < 2 ^ (prefixWord ++ tailWord_7488240).sum := by decide
  have hdescent : baseEnd_7488240 < baseStart_7488240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488244 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_7488244 : Nat := 118140960795 + 7488244 * 2 ^ 59
def prefixEnd_7488244 : Nat := 4983230072969 + 3 ^ 40 * 7488244 * 2
def baseEnd_7488244 : Nat := 1281689476715501814870733

theorem tailTrace_7488244 : CollatzResearch.WordTrace tailWord_7488244 prefixEnd_7488244 1281689476715501814870733 := by
  unfold tailWord_7488244
  simp only [CollatzResearch.WordTrace]
  refine ⟨136559348141689176551327893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182079130855585568735103857 136559348141689176551327893)
  ·
    refine ⟨6401219444141680150843495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 136559348141689176551327893 6401219444141680150843495)
    ·
      refine ⟨9601829166212520226265243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6401219444141680150843495 9601829166212520226265243)
      ·
        refine ⟨14402743749318780339397865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9601829166212520226265243 14402743749318780339397865)
        ·
          refine ⟨10802057811989085254548399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14402743749318780339397865 10802057811989085254548399)
          ·
            refine ⟨16203086717983627881822599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10802057811989085254548399 16203086717983627881822599)
            ·
              refine ⟨24304630076975441822733899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16203086717983627881822599 24304630076975441822733899)
              ·
                refine ⟨36456945115463162734100849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24304630076975441822733899 36456945115463162734100849)
                ·
                  refine ⟨27342708836597372050575637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36456945115463162734100849 27342708836597372050575637)
                  ·
                    refine ⟨1281689476715501814870733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27342708836597372050575637 1281689476715501814870733)
                    ·
                      rfl

theorem cell23_7488244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_7488244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488244 prefixEnd_7488244 := by exact prefixLift 7488244
  have htrace : WordTrace (prefixWord ++ tailWord_7488244) baseStart_7488244 baseEnd_7488244 := by
    simpa [prefixWord, tailWord_7488244, baseEnd_7488244] using wordTrace_append hprefix tailTrace_7488244
  have hstable : (prefixWord ++ tailWord_7488244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488244).length < 2 ^ (prefixWord ++ tailWord_7488244).sum := by decide
  have hdescent : baseEnd_7488244 < baseStart_7488244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488253 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_7488253 : Nat := 118140960795 + 7488253 * 2 ^ 59
def prefixEnd_7488253 : Nat := 4983230072969 + 3 ^ 40 * 7488253 * 2
def baseEnd_7488253 : Nat := 1281691017157465303133219

theorem tailTrace_7488253 : CollatzResearch.WordTrace tailWord_7488253 prefixEnd_7488253 1281691017157465303133219 := by
  unfold tailWord_7488253
  simp only [CollatzResearch.WordTrace]
  refine ⟨273119024540345747639733413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182079349693563831759822275 273119024540345747639733413)
  ·
    refine ⟨51209817101314827682450015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273119024540345747639733413 51209817101314827682450015)
    ·
      refine ⟨76814725651972241523675023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51209817101314827682450015 76814725651972241523675023)
      ·
        refine ⟨115222088477958362285512535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76814725651972241523675023 115222088477958362285512535)
        ·
          refine ⟨172833132716937543428268803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115222088477958362285512535 172833132716937543428268803)
          ·
            refine ⟨259249699075406315142403205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172833132716937543428268803 259249699075406315142403205)
            ·
              refine ⟨48609318576638684089200601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259249699075406315142403205 48609318576638684089200601)
              ·
                refine ⟨36456988932479013066900451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48609318576638684089200601 36456988932479013066900451)
                ·
                  refine ⟨54685483398718519600350677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36456988932479013066900451 54685483398718519600350677)
                  ·
                    refine ⟨1281691017157465303133219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54685483398718519600350677 1281691017157465303133219)
                    ·
                      rfl

theorem cell23_7488253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_7488253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488253 prefixEnd_7488253 := by exact prefixLift 7488253
  have htrace : WordTrace (prefixWord ++ tailWord_7488253) baseStart_7488253 baseEnd_7488253 := by
    simpa [prefixWord, tailWord_7488253, baseEnd_7488253] using wordTrace_append hprefix tailTrace_7488253
  have hstable : (prefixWord ++ tailWord_7488253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488253).length < 2 ^ (prefixWord ++ tailWord_7488253).sum := by decide
  have hdescent : baseEnd_7488253 < baseStart_7488253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488285 : List Nat := [1, 4, 2, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_7488285 : Nat := 118140960795 + 7488285 * 2 ^ 59
def prefixEnd_7488285 : Nat := 4983230072969 + 3 ^ 40 * 7488285 * 2
def baseEnd_7488285 : Nat := 3845089482853339784199511

theorem tailTrace_7488285 : CollatzResearch.WordTrace tailWord_7488285 prefixEnd_7488285 3845089482853339784199511 := by
  unfold tailWord_7488285
  simp only [CollatzResearch.WordTrace]
  refine ⟨273120191676229817104898309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182080127784153211403265539 273120191676229817104898309)
  ·
    refine ⟨51210035939293090707168433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273120191676229817104898309 51210035939293090707168433)
    ·
      refine ⟨38407526954469818030376325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51210035939293090707168433 38407526954469818030376325)
      ·
        refine ⟨7201411303963090880695561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38407526954469818030376325 7201411303963090880695561)
        ·
          refine ⟨5401058477972318160521671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7201411303963090880695561 5401058477972318160521671)
          ·
            refine ⟨8101587716958477240782507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401058477972318160521671 8101587716958477240782507)
            ·
              refine ⟨12152381575437715861173761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8101587716958477240782507 12152381575437715861173761)
              ·
                refine ⟨9114286181578286895880321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12152381575437715861173761 9114286181578286895880321)
                ·
                  refine ⟨6835714636183715171910241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9114286181578286895880321 6835714636183715171910241)
                  ·
                    refine ⟨5126785977137786378932681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6835714636183715171910241 5126785977137786378932681)
                    ·
                      refine ⟨3845089482853339784199511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5126785977137786378932681 3845089482853339784199511)
                      ·
                        rfl

theorem cell23_7488285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_7488285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488285 prefixEnd_7488285 := by exact prefixLift 7488285
  have htrace : WordTrace (prefixWord ++ tailWord_7488285) baseStart_7488285 baseEnd_7488285 := by
    simpa [prefixWord, tailWord_7488285, baseEnd_7488285] using wordTrace_append hprefix tailTrace_7488285
  have hstable : (prefixWord ++ tailWord_7488285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488285).length < 2 ^ (prefixWord ++ tailWord_7488285).sum := by decide
  have hdescent : baseEnd_7488285 < baseStart_7488285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488303 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 4]
def baseStart_7488303 : Nat := 118140960795 + 7488303 * 2 ^ 59
def prefixEnd_7488303 : Nat := 4983230072969 + 3 ^ 40 * 7488303 * 2
def baseEnd_7488303 : Nat := 3845098725505120713774427

theorem tailTrace_7488303 : CollatzResearch.WordTrace tailWord_7488303 prefixEnd_7488303 3845098725505120713774427 := by
  unfold tailWord_7488303
  simp only [CollatzResearch.WordTrace]
  refine ⟨273120848190164606179053563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182080565460109737452702375 273120848190164606179053563)
  ·
    refine ⟨409681272285246909268580345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273120848190164606179053563 409681272285246909268580345)
    ·
      refine ⟨307260954213935181951435259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409681272285246909268580345 307260954213935181951435259)
      ·
        refine ⟨460891431320902772927152889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307260954213935181951435259 460891431320902772927152889)
        ·
          refine ⟨345668573490677079695364667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460891431320902772927152889 345668573490677079695364667)
          ·
            refine ⟨518502860236015619543047001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345668573490677079695364667 518502860236015619543047001)
            ·
              refine ⟨388877145177011714657285251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518502860236015619543047001 388877145177011714657285251)
              ·
                refine ⟨583315717765517571985927877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388877145177011714657285251 583315717765517571985927877)
                ·
                  refine ⟨109371697081034544747361477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 583315717765517571985927877 109371697081034544747361477)
                  ·
                    refine ⟨20507193202693977140130277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109371697081034544747361477 20507193202693977140130277)
                    ·
                      refine ⟨3845098725505120713774427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20507193202693977140130277 3845098725505120713774427)
                      ·
                        rfl

theorem cell23_7488303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_7488303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488303 prefixEnd_7488303 := by exact prefixLift 7488303
  have htrace : WordTrace (prefixWord ++ tailWord_7488303) baseStart_7488303 baseEnd_7488303 := by
    simpa [prefixWord, tailWord_7488303, baseEnd_7488303] using wordTrace_append hprefix tailTrace_7488303
  have hstable : (prefixWord ++ tailWord_7488303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488303).length < 2 ^ (prefixWord ++ tailWord_7488303).sum := by decide
  have hdescent : baseEnd_7488303 < baseStart_7488303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488307 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 2, 4, 2]
def baseStart_7488307 : Nat := 118140960795 + 7488307 * 2 ^ 59
def prefixEnd_7488307 : Nat := 4983230072969 + 3 ^ 40 * 7488307 * 2
def baseEnd_7488307 : Nat := 3845100779427738698124409

theorem tailTrace_7488307 : CollatzResearch.WordTrace tailWord_7488307 prefixEnd_7488307 3845100779427738698124409 := by
  unfold tailWord_7488307
  simp only [CollatzResearch.WordTrace]
  refine ⟨273120994082150114862199175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182080662721433409908132783 273120994082150114862199175)
  ·
    refine ⟨409681491123225172293298763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273120994082150114862199175 409681491123225172293298763)
    ·
      refine ⟨614522236684837758439948145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409681491123225172293298763 614522236684837758439948145)
      ·
        refine ⟨460891677513628318829961109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614522236684837758439948145 460891677513628318829961109)
        ·
          refine ⟨21604297383451327445154427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 460891677513628318829961109 21604297383451327445154427)
          ·
            refine ⟨32406446075176991167731641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21604297383451327445154427 32406446075176991167731641)
            ·
              refine ⟨24304834556382743375798731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32406446075176991167731641 24304834556382743375798731)
              ·
                refine ⟨36457251834574115063698097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24304834556382743375798731 36457251834574115063698097)
                ·
                  refine ⟨27342938875930586297773573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36457251834574115063698097 27342938875930586297773573)
                  ·
                    refine ⟨5126801039236984930832545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27342938875930586297773573 5126801039236984930832545)
                    ·
                      refine ⟨3845100779427738698124409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5126801039236984930832545 3845100779427738698124409)
                      ·
                        rfl

theorem cell23_7488307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 4, 2].length) (baseStart_7488307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488307 prefixEnd_7488307 := by exact prefixLift 7488307
  have htrace : WordTrace (prefixWord ++ tailWord_7488307) baseStart_7488307 baseEnd_7488307 := by
    simpa [prefixWord, tailWord_7488307, baseEnd_7488307] using wordTrace_append hprefix tailTrace_7488307
  have hstable : (prefixWord ++ tailWord_7488307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488307).length < 2 ^ (prefixWord ++ tailWord_7488307).sum := by decide
  have hdescent : baseEnd_7488307 < baseStart_7488307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488377 : List Nat := [1, 2, 1, 3, 2, 3, 3, 2, 1, 5]
def baseStart_7488377 : Nat := 118140960795 + 7488377 * 2 ^ 59
def prefixEnd_7488377 : Nat := 4983230072969 + 3 ^ 40 * 7488377 * 2
def baseEnd_7488377 : Nat := 1281712241024517808083029

theorem tailTrace_7488377 : CollatzResearch.WordTrace tailWord_7488377 prefixEnd_7488377 1281712241024517808083029 := by
  unfold tailWord_7488377
  simp only [CollatzResearch.WordTrace]
  refine ⟨273123547191896516817247385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182082364794597677878164923 273123547191896516817247385)
  ·
    refine ⟨204842660393922387612935539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273123547191896516817247385 204842660393922387612935539)
    ·
      refine ⟨307263990590883581419403309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204842660393922387612935539 307263990590883581419403309)
      ·
        refine ⟨115223996471581343032276241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307263990590883581419403309 115223996471581343032276241)
        ·
          refine ⟨86417997353686007274207181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115223996471581343032276241 86417997353686007274207181)
          ·
            refine ⟨32406749007632252727827693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86417997353686007274207181 32406749007632252727827693)
            ·
              refine ⟨12152530877862094772935385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32406749007632252727827693 12152530877862094772935385)
              ·
                refine ⟨9114398158396571079701539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12152530877862094772935385 9114398158396571079701539)
                ·
                  refine ⟨13671597237594856619552309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9114398158396571079701539 13671597237594856619552309)
                  ·
                    refine ⟨1281712241024517808083029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13671597237594856619552309 1281712241024517808083029)
                    ·
                      rfl

theorem cell23_7488377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 5].length) (baseStart_7488377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488377 prefixEnd_7488377 := by exact prefixLift 7488377
  have htrace : WordTrace (prefixWord ++ tailWord_7488377) baseStart_7488377 baseEnd_7488377 := by
    simpa [prefixWord, tailWord_7488377, baseEnd_7488377] using wordTrace_append hprefix tailTrace_7488377
  have hstable : (prefixWord ++ tailWord_7488377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488377).length < 2 ^ (prefixWord ++ tailWord_7488377).sum := by decide
  have hdescent : baseEnd_7488377 < baseStart_7488377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488437 : List Nat := [1, 3, 3, 2, 1, 1, 5, 7]
def baseStart_7488437 : Nat := 118140960795 + 7488437 * 2 ^ 59
def prefixEnd_7488437 : Nat := 4983230072969 + 3 ^ 40 * 7488437 * 2
def baseEnd_7488437 : Nat := 142413612293067525536993

theorem tailTrace_7488437 : CollatzResearch.WordTrace tailWord_7488437 prefixEnd_7488437 142413612293067525536993 := by
  unfold tailWord_7488437
  simp only [CollatzResearch.WordTrace]
  refine ⟨273125735571679147064431565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182083823714452764709621043 273125735571679147064431565)
  ·
    refine ⟨102422150839379680149161837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273125735571679147064431565 102422150839379680149161837)
    ·
      refine ⟨38408306564767380055935689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102422150839379680149161837 38408306564767380055935689)
      ·
        refine ⟨28806229923575535041951767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38408306564767380055935689 28806229923575535041951767)
        ·
          refine ⟨43209344885363302562927651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28806229923575535041951767 43209344885363302562927651)
          ·
            refine ⟨64814017328044953844391477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43209344885363302562927651 64814017328044953844391477)
            ·
              refine ⟨6076314124504214422911701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64814017328044953844391477 6076314124504214422911701)
              ·
                refine ⟨142413612293067525536993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6076314124504214422911701 142413612293067525536993)
                ·
                  rfl

theorem cell23_7488437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 7].length) (baseStart_7488437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488437 prefixEnd_7488437 := by exact prefixLift 7488437
  have htrace : WordTrace (prefixWord ++ tailWord_7488437) baseStart_7488437 baseEnd_7488437 := by
    simpa [prefixWord, tailWord_7488437, baseEnd_7488437] using wordTrace_append hprefix tailTrace_7488437
  have hstable : (prefixWord ++ tailWord_7488437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488437).length < 2 ^ (prefixWord ++ tailWord_7488437).sum := by decide
  have hdescent : baseEnd_7488437 < baseStart_7488437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488448 : List Nat := [2, 1, 1, 2, 3, 4, 2, 3, 1, 2, 2]
def baseStart_7488448 : Nat := 118140960795 + 7488448 * 2 ^ 59
def prefixEnd_7488448 : Nat := 4983230072969 + 3 ^ 40 * 7488448 * 2
def baseEnd_7488448 : Nat := 3845173180200022646461261

theorem tailTrace_7488448 : CollatzResearch.WordTrace tailWord_7488448 prefixEnd_7488448 3845173180200022646461261 := by
  unfold tailWord_7488448
  simp only [CollatzResearch.WordTrace]
  refine ⟨136563068387319647971540999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182084091183092863962054665 136563068387319647971540999)
  ·
    refine ⟨204844602580979471957311499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136563068387319647971540999 204844602580979471957311499)
    ·
      refine ⟨307266903871469207935967249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204844602580979471957311499 307266903871469207935967249)
      ·
        refine ⟨230450177903601905951975437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307266903871469207935967249 230450177903601905951975437)
        ·
          refine ⟨86418816713850714731990789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230450177903601905951975437 86418816713850714731990789)
          ·
            refine ⟨16203528133847009012248273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86418816713850714731990789 16203528133847009012248273)
            ·
              refine ⟨12152646100385256759186205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16203528133847009012248273 12152646100385256759186205)
              ·
                refine ⟨4557242287644471284694827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12152646100385256759186205 4557242287644471284694827)
                ·
                  refine ⟨6835863431466706927042241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4557242287644471284694827 6835863431466706927042241)
                  ·
                    refine ⟨5126897573600030195281681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6835863431466706927042241 5126897573600030195281681)
                    ·
                      refine ⟨3845173180200022646461261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5126897573600030195281681 3845173180200022646461261)
                      ·
                        rfl

theorem cell23_7488448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 1, 2, 2].length) (baseStart_7488448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488448 prefixEnd_7488448 := by exact prefixLift 7488448
  have htrace : WordTrace (prefixWord ++ tailWord_7488448) baseStart_7488448 baseEnd_7488448 := by
    simpa [prefixWord, tailWord_7488448, baseEnd_7488448] using wordTrace_append hprefix tailTrace_7488448
  have hstable : (prefixWord ++ tailWord_7488448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488448).length < 2 ^ (prefixWord ++ tailWord_7488448).sum := by decide
  have hdescent : baseEnd_7488448 < baseStart_7488448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488537 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 2, 3, 3]
def baseStart_7488537 : Nat := 118140960795 + 7488537 * 2 ^ 59
def prefixEnd_7488537 : Nat := 4983230072969 + 3 ^ 40 * 7488537 * 2
def baseEnd_7488537 : Nat := 3845218879978272798248351

theorem tailTrace_7488537 : CollatzResearch.WordTrace tailWord_7488537 prefixEnd_7488537 3845218879978272798248351 := by
  unfold tailWord_7488537
  simp only [CollatzResearch.WordTrace]
  refine ⟨273129382871316864143071865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182086255247544576095381243 273129382871316864143071865)
  ·
    refine ⟨204847037153487648107303899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273129382871316864143071865 204847037153487648107303899)
    ·
      refine ⟨307270555730231472160955849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204847037153487648107303899 307270555730231472160955849)
      ·
        refine ⟨230452916797673604120716887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307270555730231472160955849 230452916797673604120716887)
        ·
          refine ⟨345679375196510406181075331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230452916797673604120716887 345679375196510406181075331)
          ·
            refine ⟨518519062794765609271612997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345679375196510406181075331 518519062794765609271612997)
            ·
              refine ⟨97222324274018551738427437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 518519062794765609271612997 97222324274018551738427437)
              ·
                refine ⟨36458371602756956901910289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97222324274018551738427437 36458371602756956901910289)
                ·
                  refine ⟨27343778702067717676432717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36458371602756956901910289 27343778702067717676432717)
                  ·
                    refine ⟨10253917013275394128662269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27343778702067717676432717 10253917013275394128662269)
                    ·
                      refine ⟨3845218879978272798248351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10253917013275394128662269 3845218879978272798248351)
                      ·
                        rfl

theorem cell23_7488537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_7488537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488537 prefixEnd_7488537 := by exact prefixLift 7488537
  have htrace : WordTrace (prefixWord ++ tailWord_7488537) baseStart_7488537 baseEnd_7488537 := by
    simpa [prefixWord, tailWord_7488537, baseEnd_7488537] using wordTrace_append hprefix tailTrace_7488537
  have hstable : (prefixWord ++ tailWord_7488537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488537).length < 2 ^ (prefixWord ++ tailWord_7488537).sum := by decide
  have hdescent : baseEnd_7488537 < baseStart_7488537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488627 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 3]
def baseStart_7488627 : Nat := 118140960795 + 7488627 * 2 ^ 59
def prefixEnd_7488627 : Nat := 4983230072969 + 3 ^ 40 * 7488627 * 2
def baseEnd_7488627 : Nat := 3845265093237177446122937

theorem tailTrace_7488627 : CollatzResearch.WordTrace tailWord_7488627 prefixEnd_7488627 3845265093237177446122937 := by
  unfold tailWord_7488627
  simp only [CollatzResearch.WordTrace]
  refine ⟨273132665440990809513848135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182088443627327206342565423 273132665440990809513848135)
  ·
    refine ⟨409698998161486214270772203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273132665440990809513848135 409698998161486214270772203)
    ·
      refine ⟨614548497242229321406158305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409698998161486214270772203 614548497242229321406158305)
      ·
        refine ⟨460911372931671991054618729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614548497242229321406158305 460911372931671991054618729)
        ·
          refine ⟨345683529698753993290964047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460911372931671991054618729 345683529698753993290964047)
          ·
            refine ⟨518525294548130989936446071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345683529698753993290964047 518525294548130989936446071)
            ·
              refine ⟨777787941822196484904669107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518525294548130989936446071 777787941822196484904669107)
              ·
                refine ⟨1166681912733294727357003661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777787941822196484904669107 1166681912733294727357003661)
                ·
                  refine ⟨437505717274985522758876373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166681912733294727357003661 437505717274985522758876373)
                  ·
                    refine ⟨10254040248632473189661165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 437505717274985522758876373 10254040248632473189661165)
                    ·
                      refine ⟨3845265093237177446122937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10254040248632473189661165 3845265093237177446122937)
                      ·
                        rfl

theorem cell23_7488627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 3].length) (baseStart_7488627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488627 prefixEnd_7488627 := by exact prefixLift 7488627
  have htrace : WordTrace (prefixWord ++ tailWord_7488627) baseStart_7488627 baseEnd_7488627 := by
    simpa [prefixWord, tailWord_7488627, baseEnd_7488627] using wordTrace_append hprefix tailTrace_7488627
  have hstable : (prefixWord ++ tailWord_7488627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488627).length < 2 ^ (prefixWord ++ tailWord_7488627).sum := by decide
  have hdescent : baseEnd_7488627 < baseStart_7488627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488637 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_7488637 : Nat := 118140960795 + 7488637 * 2 ^ 59
def prefixEnd_7488637 : Nat := 4983230072969 + 3 ^ 40 * 7488637 * 2
def baseEnd_7488637 : Nat := 3845270228043722406997891

theorem tailTrace_7488637 : CollatzResearch.WordTrace tailWord_7488637 prefixEnd_7488637 3845270228043722406997891 := by
  unfold tailWord_7488637
  simp only [CollatzResearch.WordTrace]
  refine ⟨273133030170954581221712165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182088686780636387481141443 273133030170954581221712165)
  ·
    refine ⟨51212443157053983979071031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273133030170954581221712165 51212443157053983979071031)
    ·
      refine ⟨76818664735580975968606547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51212443157053983979071031 76818664735580975968606547)
      ·
        refine ⟨115227997103371463952909821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76818664735580975968606547 115227997103371463952909821)
        ·
          refine ⟨43210498913764298982341183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115227997103371463952909821 43210498913764298982341183)
          ·
            refine ⟨64815748370646448473511775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43210498913764298982341183 64815748370646448473511775)
            ·
              refine ⟨97223622555969672710267663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64815748370646448473511775 97223622555969672710267663)
              ·
                refine ⟨145835433833954509065401495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97223622555969672710267663 145835433833954509065401495)
                ·
                  refine ⟨218753150750931763598102243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145835433833954509065401495 218753150750931763598102243)
                  ·
                    refine ⟨328129726126397645397153365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218753150750931763598102243 328129726126397645397153365)
                    ·
                      refine ⟨3845270228043722406997891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 328129726126397645397153365 3845270228043722406997891)
                      ·
                        rfl

theorem cell23_7488637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_7488637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488637 prefixEnd_7488637 := by exact prefixLift 7488637
  have htrace : WordTrace (prefixWord ++ tailWord_7488637) baseStart_7488637 baseEnd_7488637 := by
    simpa [prefixWord, tailWord_7488637, baseEnd_7488637] using wordTrace_append hprefix tailTrace_7488637
  have hstable : (prefixWord ++ tailWord_7488637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488637).length < 2 ^ (prefixWord ++ tailWord_7488637).sum := by decide
  have hdescent : baseEnd_7488637 < baseStart_7488637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488695 : List Nat := [1, 1, 3, 1, 4, 1, 5, 2, 1, 1, 3]
def baseStart_7488695 : Nat := 118140960795 + 7488695 * 2 ^ 59
def prefixEnd_7488695 : Nat := 4983230072969 + 3 ^ 40 * 7488695 * 2
def baseEnd_7488695 : Nat := 3845300009921683180072625

theorem tailTrace_7488695 : CollatzResearch.WordTrace tailWord_7488695 prefixEnd_7488695 3845300009921683180072625 := by
  unfold tailWord_7488695
  simp only [CollatzResearch.WordTrace]
  refine ⟨273135145604744457127323539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182090097069829638084882359 273135145604744457127323539)
  ·
    refine ⟨409702718407116685690985309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273135145604744457127323539 409702718407116685690985309)
    ·
      refine ⟨153638519402668757134119491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409702718407116685690985309 153638519402668757134119491)
      ·
        refine ⟨230457779104003135701179237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153638519402668757134119491 230457779104003135701179237)
        ·
          refine ⟨43210833582000587943971107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230457779104003135701179237 43210833582000587943971107)
          ·
            refine ⟨64816250373000881915956661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43210833582000587943971107 64816250373000881915956661)
            ·
              refine ⟨6076523472468832679620937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64816250373000881915956661 6076523472468832679620937)
              ·
                refine ⟨4557392604351624509715703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6076523472468832679620937 4557392604351624509715703)
                ·
                  refine ⟨6836088906527436764573555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4557392604351624509715703 6836088906527436764573555)
                  ·
                    refine ⟨10254133359791155146860333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6836088906527436764573555 10254133359791155146860333)
                    ·
                      refine ⟨3845300009921683180072625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10254133359791155146860333 3845300009921683180072625)
                      ·
                        rfl

theorem cell23_7488695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 1, 1, 3].length) (baseStart_7488695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488695 prefixEnd_7488695 := by exact prefixLift 7488695
  have htrace : WordTrace (prefixWord ++ tailWord_7488695) baseStart_7488695 baseEnd_7488695 := by
    simpa [prefixWord, tailWord_7488695, baseEnd_7488695] using wordTrace_append hprefix tailTrace_7488695
  have hstable : (prefixWord ++ tailWord_7488695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488695).length < 2 ^ (prefixWord ++ tailWord_7488695).sum := by decide
  have hdescent : baseEnd_7488695 < baseStart_7488695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488714 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_7488714 : Nat := 118140960795 + 7488714 * 2 ^ 59
def prefixEnd_7488714 : Nat := 4983230072969 + 3 ^ 40 * 7488714 * 2
def baseEnd_7488714 : Nat := 3845309766054118605735037

theorem tailTrace_7488714 : CollatzResearch.WordTrace tailWord_7488714 prefixEnd_7488714 3845309766054118605735037 := by
  unfold tailWord_7488714
  simp only [CollatzResearch.WordTrace]
  refine ⟨68283959647918905843066299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182090559061117082248176797 68283959647918905843066299)
  ·
    refine ⟨102425939471878358764599449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68283959647918905843066299 102425939471878358764599449)
    ·
      refine ⟨76819454603908769073449587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102425939471878358764599449 76819454603908769073449587)
      ·
        refine ⟨115229181905863153610174381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76819454603908769073449587 115229181905863153610174381)
        ·
          refine ⟨43210943214698682603815393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115229181905863153610174381 43210943214698682603815393)
          ·
            refine ⟨32408207411024011952861545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43210943214698682603815393 32408207411024011952861545)
            ·
              refine ⟨24306155558268008964646159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32408207411024011952861545 24306155558268008964646159)
              ·
                refine ⟨36459233337402013446969239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24306155558268008964646159 36459233337402013446969239)
                ·
                  refine ⟨54688850006103020170453859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36459233337402013446969239 54688850006103020170453859)
                  ·
                    refine ⟨82033275009154530255680789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54688850006103020170453859 82033275009154530255680789)
                    ·
                      refine ⟨3845309766054118605735037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82033275009154530255680789 3845309766054118605735037)
                      ·
                        rfl

theorem cell23_7488714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_7488714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488714 prefixEnd_7488714 := by exact prefixLift 7488714
  have htrace : WordTrace (prefixWord ++ tailWord_7488714) baseStart_7488714 baseEnd_7488714 := by
    simpa [prefixWord, tailWord_7488714, baseEnd_7488714] using wordTrace_append hprefix tailTrace_7488714
  have hstable : (prefixWord ++ tailWord_7488714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488714).length < 2 ^ (prefixWord ++ tailWord_7488714).sum := by decide
  have hdescent : baseEnd_7488714 < baseStart_7488714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488761 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 5, 3, 2]
def baseStart_7488761 : Nat := 118140960795 + 7488761 * 2 ^ 59
def prefixEnd_7488761 : Nat := 4983230072969 + 3 ^ 40 * 7488761 * 2
def baseEnd_7488761 : Nat := 3845333899644879921847321

theorem tailTrace_7488761 : CollatzResearch.WordTrace tailWord_7488761 prefixEnd_7488761 3845333899644879921847321 := by
  unfold tailWord_7488761
  simp only [CollatzResearch.WordTrace]
  refine ⟨273137552822505350399226137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182091701881670233599484091 273137552822505350399226137)
  ·
    refine ⟨204853164616879012799419603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273137552822505350399226137 204853164616879012799419603)
    ·
      refine ⟨307279746925318519199129405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204853164616879012799419603 307279746925318519199129405)
      ·
        refine ⟨115229905096994444699673527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307279746925318519199129405 115229905096994444699673527)
        ·
          refine ⟨172844857645491667049510291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115229905096994444699673527 172844857645491667049510291)
          ·
            refine ⟨259267286468237500574265437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172844857645491667049510291 259267286468237500574265437)
            ·
              refine ⟨97225232425589062715349539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259267286468237500574265437 97225232425589062715349539)
              ·
                refine ⟨145837848638383594073024309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97225232425589062715349539 145837848638383594073024309)
                ·
                  refine ⟨13672298309848461944346029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145837848638383594073024309 13672298309848461944346029)
                  ·
                    refine ⟨5127111866193173229129761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13672298309848461944346029 5127111866193173229129761)
                    ·
                      refine ⟨3845333899644879921847321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5127111866193173229129761 3845333899644879921847321)
                      ·
                        rfl

theorem cell23_7488761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_7488761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488761 prefixEnd_7488761 := by exact prefixLift 7488761
  have htrace : WordTrace (prefixWord ++ tailWord_7488761) baseStart_7488761 baseEnd_7488761 := by
    simpa [prefixWord, tailWord_7488761, baseEnd_7488761] using wordTrace_append hprefix tailTrace_7488761
  have hstable : (prefixWord ++ tailWord_7488761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488761).length < 2 ^ (prefixWord ++ tailWord_7488761).sum := by decide
  have hdescent : baseEnd_7488761 < baseStart_7488761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488778 : List Nat := [3, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2]
def baseStart_7488778 : Nat := 118140960795 + 7488778 * 2 ^ 59
def prefixEnd_7488778 : Nat := 4983230072969 + 3 ^ 40 * 7488778 * 2
def baseEnd_7488778 : Nat := 3845342628816006355334743

theorem tailTrace_7488778 : CollatzResearch.WordTrace tailWord_7488778 prefixEnd_7488778 3845342628816006355334743 := by
  unfold tailWord_7488778
  simp only [CollatzResearch.WordTrace]
  refine ⟨68284543215860940575648747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182092115242295841535063325 68284543215860940575648747)
  ·
    refine ⟨102426814823791410863473121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68284543215860940575648747 102426814823791410863473121)
    ·
      refine ⟨76820111117843558147604841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102426814823791410863473121 76820111117843558147604841)
      ·
        refine ⟨57615083338382668610703631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76820111117843558147604841 57615083338382668610703631)
        ·
          refine ⟨86422625007574002916055447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57615083338382668610703631 86422625007574002916055447)
          ·
            refine ⟨129633937511361004374083171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86422625007574002916055447 129633937511361004374083171)
            ·
              refine ⟨194450906267041506561124757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129633937511361004374083171 194450906267041506561124757)
              ·
                refine ⟨9114886231267570620052723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194450906267041506561124757 9114886231267570620052723)
                ·
                  refine ⟨13672329346901355930079085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9114886231267570620052723 13672329346901355930079085)
                  ·
                    refine ⟨5127123505088008473779657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13672329346901355930079085 5127123505088008473779657)
                    ·
                      refine ⟨3845342628816006355334743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5127123505088008473779657 3845342628816006355334743)
                      ·
                        rfl

theorem cell23_7488778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_7488778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488778 prefixEnd_7488778 := by exact prefixLift 7488778
  have htrace : WordTrace (prefixWord ++ tailWord_7488778) baseStart_7488778 baseEnd_7488778 := by
    simpa [prefixWord, tailWord_7488778, baseEnd_7488778] using wordTrace_append hprefix tailTrace_7488778
  have hstable : (prefixWord ++ tailWord_7488778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488778).length < 2 ^ (prefixWord ++ tailWord_7488778).sum := by decide
  have hdescent : baseEnd_7488778 < baseStart_7488778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488786 : List Nat := [3, 2, 4, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7488786 : Nat := 118140960795 + 7488786 * 2 ^ 59
def prefixEnd_7488786 : Nat := 4983230072969 + 3 ^ 40 * 7488786 * 2
def baseEnd_7488786 : Nat := 3845346736661242324034707

theorem tailTrace_7488786 : CollatzResearch.WordTrace tailWord_7488786 prefixEnd_7488786 3845346736661242324034707 := by
  unfold tailWord_7488786
  simp only [CollatzResearch.WordTrace]
  refine ⟨68284616161853694917221553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182092309764943186445924141 68284616161853694917221553)
  ·
    refine ⟨51213462121390271187916165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68284616161853694917221553 51213462121390271187916165)
    ·
      refine ⟨9602524147760675847734281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51213462121390271187916165 9602524147760675847734281)
      ·
        refine ⟨7201893110820506885800711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9602524147760675847734281 7201893110820506885800711)
        ·
          refine ⟨10802839666230760328701067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7201893110820506885800711 10802839666230760328701067)
          ·
            refine ⟨16204259499346140493051601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10802839666230760328701067 16204259499346140493051601)
            ·
              refine ⟨12153194624509605369788701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16204259499346140493051601 12153194624509605369788701)
              ·
                refine ⟨4557447984191102013670763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12153194624509605369788701 4557447984191102013670763)
                ·
                  refine ⟨6836171976286653020506145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4557447984191102013670763 6836171976286653020506145)
                  ·
                    refine ⟨5127128982214989765379609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6836171976286653020506145 5127128982214989765379609)
                    ·
                      refine ⟨3845346736661242324034707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5127128982214989765379609 3845346736661242324034707)
                      ·
                        rfl

theorem cell23_7488786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7488786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488786 prefixEnd_7488786 := by exact prefixLift 7488786
  have htrace : WordTrace (prefixWord ++ tailWord_7488786) baseStart_7488786 baseEnd_7488786 := by
    simpa [prefixWord, tailWord_7488786, baseEnd_7488786] using wordTrace_append hprefix tailTrace_7488786
  have hstable : (prefixWord ++ tailWord_7488786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488786).length < 2 ^ (prefixWord ++ tailWord_7488786).sum := by decide
  have hdescent : baseEnd_7488786 < baseStart_7488786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488802 : List Nat := [3, 3, 1, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_7488802 : Nat := 118140960795 + 7488802 * 2 ^ 59
def prefixEnd_7488802 : Nat := 4983230072969 + 3 ^ 40 * 7488802 * 2
def baseEnd_7488802 : Nat := 3845354952351714261434633

theorem tailTrace_7488802 : CollatzResearch.WordTrace tailWord_7488802 prefixEnd_7488802 3845354952351714261434633 := by
  unfold tailWord_7488802
  simp only [CollatzResearch.WordTrace]
  refine ⟨68284762053839203600367165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182092698810237876267645773 68284762053839203600367165)
  ·
    refine ⟨25606785770189701350137687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68284762053839203600367165 25606785770189701350137687)
    ·
      refine ⟨38410178655284552025206531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25606785770189701350137687 38410178655284552025206531)
      ·
        refine ⟨57615267982926828037809797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38410178655284552025206531 57615267982926828037809797)
        ·
          refine ⟨10802862746798780257089337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57615267982926828037809797 10802862746798780257089337)
          ·
            refine ⟨8102147060099085192817003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10802862746798780257089337 8102147060099085192817003)
            ·
              refine ⟨12153220590148627789225505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8102147060099085192817003 12153220590148627789225505)
              ·
                refine ⟨9114915442611470841919129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12153220590148627789225505 9114915442611470841919129)
                ·
                  refine ⟨6836186581958603131439347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9114915442611470841919129 6836186581958603131439347)
                  ·
                    refine ⟨10254279872937904697159021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6836186581958603131439347 10254279872937904697159021)
                    ·
                      refine ⟨3845354952351714261434633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10254279872937904697159021 3845354952351714261434633)
                      ·
                        rfl

theorem cell23_7488802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_7488802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488802 prefixEnd_7488802 := by exact prefixLift 7488802
  have htrace : WordTrace (prefixWord ++ tailWord_7488802) baseStart_7488802 baseEnd_7488802 := by
    simpa [prefixWord, tailWord_7488802, baseEnd_7488802] using wordTrace_append hprefix tailTrace_7488802
  have hstable : (prefixWord ++ tailWord_7488802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488802).length < 2 ^ (prefixWord ++ tailWord_7488802).sum := by decide
  have hdescent : baseEnd_7488802 < baseStart_7488802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488821 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_7488821 : Nat := 118140960795 + 7488821 * 2 ^ 59
def prefixEnd_7488821 : Nat := 4983230072969 + 3 ^ 40 * 7488821 * 2
def baseEnd_7488821 : Nat := 3845364708484149687097045

theorem tailTrace_7488821 : CollatzResearch.WordTrace tailWord_7488821 prefixEnd_7488821 3845364708484149687097045 := by
  unfold tailWord_7488821
  simp only [CollatzResearch.WordTrace]
  refine ⟨273139741202287980646410317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182093160801525320430940211 273139741202287980646410317)
  ·
    refine ⟨102427402950857992742403869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273139741202287980646410317 102427402950857992742403869)
    ·
      refine ⟨38410276106571747278401451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102427402950857992742403869 38410276106571747278401451)
      ·
        refine ⟨57615414159857620917602177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38410276106571747278401451 57615414159857620917602177)
        ·
          refine ⟨43211560619893215688201633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57615414159857620917602177 43211560619893215688201633)
          ·
            refine ⟨32408670464919911766151225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43211560619893215688201633 32408670464919911766151225)
            ·
              refine ⟨24306502848689933824613419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32408670464919911766151225 24306502848689933824613419)
              ·
                refine ⟨36459754273034900736920129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24306502848689933824613419 36459754273034900736920129)
                ·
                  refine ⟨27344815704776175552690097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36459754273034900736920129 27344815704776175552690097)
                  ·
                    refine ⟨20508611778582131664517573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27344815704776175552690097 20508611778582131664517573)
                    ·
                      refine ⟨3845364708484149687097045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20508611778582131664517573 3845364708484149687097045)
                      ·
                        rfl

theorem cell23_7488821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_7488821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488821 prefixEnd_7488821 := by exact prefixLift 7488821
  have htrace : WordTrace (prefixWord ++ tailWord_7488821) baseStart_7488821 baseEnd_7488821 := by
    simpa [prefixWord, tailWord_7488821, baseEnd_7488821] using wordTrace_append hprefix tailTrace_7488821
  have hstable : (prefixWord ++ tailWord_7488821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488821).length < 2 ^ (prefixWord ++ tailWord_7488821).sum := by decide
  have hdescent : baseEnd_7488821 < baseStart_7488821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488845 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_7488845 : Nat := 118140960795 + 7488845 * 2 ^ 59
def prefixEnd_7488845 : Nat := 4983230072969 + 3 ^ 40 * 7488845 * 2
def baseEnd_7488845 : Nat := 3845377032019857593196935

theorem tailTrace_7488845 : CollatzResearch.WordTrace tailWord_7488845 prefixEnd_7488845 3845377032019857593196935 := by
  unfold tailWord_7488845
  simp only [CollatzResearch.WordTrace]
  refine ⟨273140616554201032745283989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182093744369467355163522659 273140616554201032745283989)
  ·
    refine ⟨12803466400978173409935187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 273140616554201032745283989 12803466400978173409935187)
    ·
      refine ⟨19205199601467260114902781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12803466400978173409935187 19205199601467260114902781)
      ·
        refine ⟨7201949850550222543088543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19205199601467260114902781 7201949850550222543088543)
        ·
          refine ⟨10802924775825333814632815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7201949850550222543088543 10802924775825333814632815)
          ·
            refine ⟨16204387163738000721949223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10802924775825333814632815 16204387163738000721949223)
            ·
              refine ⟨24306580745607001082923835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16204387163738000721949223 24306580745607001082923835)
              ·
                refine ⟨36459871118410501624385753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24306580745607001082923835 36459871118410501624385753)
                ·
                  refine ⟨27344903338807876218289315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36459871118410501624385753 27344903338807876218289315)
                  ·
                    refine ⟨41017355008211814327433973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27344903338807876218289315 41017355008211814327433973)
                    ·
                      refine ⟨3845377032019857593196935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41017355008211814327433973 3845377032019857593196935)
                      ·
                        rfl

theorem cell23_7488845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_7488845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488845 prefixEnd_7488845 := by exact prefixLift 7488845
  have htrace : WordTrace (prefixWord ++ tailWord_7488845) baseStart_7488845 baseEnd_7488845 := by
    simpa [prefixWord, tailWord_7488845, baseEnd_7488845] using wordTrace_append hprefix tailTrace_7488845
  have hstable : (prefixWord ++ tailWord_7488845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488845).length < 2 ^ (prefixWord ++ tailWord_7488845).sum := by decide
  have hdescent : baseEnd_7488845 < baseStart_7488845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488891 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 5, 4]
def baseStart_7488891 : Nat := 118140960795 + 7488891 * 2 ^ 59
def prefixEnd_7488891 : Nat := 4983230072969 + 3 ^ 40 * 7488891 * 2
def baseEnd_7488891 : Nat := 1281800217376654804407241

theorem tailTrace_7488891 : CollatzResearch.WordTrace tailWord_7488891 prefixEnd_7488891 1281800217376654804407241 := by
  unfold tailWord_7488891
  simp only [CollatzResearch.WordTrace]
  refine ⟨273142294312034382601458527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182094862874689588400972351 273142294312034382601458527)
  ·
    refine ⟨409713441468051573902187791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273142294312034382601458527 409713441468051573902187791)
    ·
      refine ⟨614570162202077360853281687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409713441468051573902187791 614570162202077360853281687)
      ·
        refine ⟨921855243303116041279922531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614570162202077360853281687 921855243303116041279922531)
        ·
          refine ⟨1382782864954674061919883797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921855243303116041279922531 1382782864954674061919883797)
          ·
            refine ⟨64817946794750346652494553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1382782864954674061919883797 64817946794750346652494553)
            ·
              refine ⟨48613460096062759989370915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64817946794750346652494553 48613460096062759989370915)
              ·
                refine ⟨72920190144094139984056373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48613460096062759989370915 72920190144094139984056373)
                ·
                  refine ⟨6836267826008825623505285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72920190144094139984056373 6836267826008825623505285)
                  ·
                    refine ⟨1281800217376654804407241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6836267826008825623505285 1281800217376654804407241)
                    ·
                      rfl

theorem cell23_7488891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 4].length) (baseStart_7488891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488891 prefixEnd_7488891 := by exact prefixLift 7488891
  have htrace : WordTrace (prefixWord ++ tailWord_7488891) baseStart_7488891 baseEnd_7488891 := by
    simpa [prefixWord, tailWord_7488891, baseEnd_7488891] using wordTrace_append hprefix tailTrace_7488891
  have hstable : (prefixWord ++ tailWord_7488891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488891).length < 2 ^ (prefixWord ++ tailWord_7488891).sum := by decide
  have hdescent : baseEnd_7488891 < baseStart_7488891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488901 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 1, 4, 3]
def baseStart_7488901 : Nat := 118140960795 + 7488901 * 2 ^ 59
def prefixEnd_7488901 : Nat := 4983230072969 + 3 ^ 40 * 7488901 * 2
def baseEnd_7488901 : Nat := 3845405786936509374096677

theorem tailTrace_7488901 : CollatzResearch.WordTrace tailWord_7488901 prefixEnd_7488901 3845405786936509374096677 := by
  unfold tailWord_7488901
  simp only [CollatzResearch.WordTrace]
  refine ⟨273142659041998154309322557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182095106027998769539548371 273142659041998154309322557)
  ·
    refine ⟨102428497140749307865995959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273142659041998154309322557 102428497140749307865995959)
    ·
      refine ⟨153642745711123961798993939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102428497140749307865995959 153642745711123961798993939)
      ·
        refine ⟨230464118566685942698490909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153642745711123961798993939 230464118566685942698490909)
        ·
          refine ⟨86424044462507228511934091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230464118566685942698490909 86424044462507228511934091)
          ·
            refine ⟨129636066693760842767901137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86424044462507228511934091 129636066693760842767901137)
            ·
              refine ⟨97227050020320632075925853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129636066693760842767901137 97227050020320632075925853)
              ·
                refine ⟨36460143757620237028472195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97227050020320632075925853 36460143757620237028472195)
                ·
                  refine ⟨54690215636430355542708293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36460143757620237028472195 54690215636430355542708293)
                  ·
                    refine ⟨10254415431830691664257805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54690215636430355542708293 10254415431830691664257805)
                    ·
                      refine ⟨3845405786936509374096677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10254415431830691664257805 3845405786936509374096677)
                      ·
                        rfl

theorem cell23_7488901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_7488901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488901 prefixEnd_7488901 := by exact prefixLift 7488901
  have htrace : WordTrace (prefixWord ++ tailWord_7488901) baseStart_7488901 baseEnd_7488901 := by
    simpa [prefixWord, tailWord_7488901, baseEnd_7488901] using wordTrace_append hprefix tailTrace_7488901
  have hstable : (prefixWord ++ tailWord_7488901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488901).length < 2 ^ (prefixWord ++ tailWord_7488901).sum := by decide
  have hdescent : baseEnd_7488901 < baseStart_7488901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488921 : List Nat := [1, 2, 1, 2, 1, 5, 1, 4, 6]
def baseStart_7488921 : Nat := 118140960795 + 7488921 * 2 ^ 59
def prefixEnd_7488921 : Nat := 4983230072969 + 3 ^ 40 * 7488921 * 2
def baseEnd_7488921 : Nat := 427268450727733255094065

theorem tailTrace_7488921 : CollatzResearch.WordTrace tailWord_7488921 prefixEnd_7488921 427268450727733255094065 := by
  unfold tailWord_7488921
  simp only [CollatzResearch.WordTrace]
  refine ⟨273143388501925697725050617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182095592334617131816700411 273143388501925697725050617)
  ·
    refine ⟨204857541376444273293787963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273143388501925697725050617 204857541376444273293787963)
    ·
      refine ⟨307286312064666409940681945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204857541376444273293787963 307286312064666409940681945)
      ·
        refine ⟨230464734048499807455511459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307286312064666409940681945 230464734048499807455511459)
        ·
          refine ⟨345697101072749711183267189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230464734048499807455511459 345697101072749711183267189)
          ·
            refine ⟨32409103225570285423431299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 345697101072749711183267189 32409103225570285423431299)
            ·
              refine ⟨48613654838355428135146949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32409103225570285423431299 48613654838355428135146949)
              ·
                refine ⟨9115060282191642775340053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48613654838355428135146949 9115060282191642775340053)
                ·
                  refine ⟨427268450727733255094065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9115060282191642775340053 427268450727733255094065)
                  ·
                    rfl

theorem cell23_7488921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 6].length) (baseStart_7488921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488921 prefixEnd_7488921 := by exact prefixLift 7488921
  have htrace : WordTrace (prefixWord ++ tailWord_7488921) baseStart_7488921 baseEnd_7488921 := by
    simpa [prefixWord, tailWord_7488921, baseEnd_7488921] using wordTrace_append hprefix tailTrace_7488921
  have hstable : (prefixWord ++ tailWord_7488921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488921).length < 2 ^ (prefixWord ++ tailWord_7488921).sum := by decide
  have hdescent : baseEnd_7488921 < baseStart_7488921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488951 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 3, 5]
def baseStart_7488951 : Nat := 118140960795 + 7488951 * 2 ^ 59
def prefixEnd_7488951 : Nat := 4983230072969 + 3 ^ 40 * 7488951 * 2
def baseEnd_7488951 : Nat := 1281810486989744726157149

theorem tailTrace_7488951 : CollatzResearch.WordTrace tailWord_7488951 prefixEnd_7488951 1281810486989744726157149 := by
  unfold tailWord_7488951
  simp only [CollatzResearch.WordTrace]
  refine ⟨273144482691817012848642707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182096321794544675232428471 273144482691817012848642707)
  ·
    refine ⟨409716724037725519272964061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273144482691817012848642707 409716724037725519272964061)
    ·
      refine ⟨153643771514147069727361523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409716724037725519272964061 153643771514147069727361523)
      ·
        refine ⟨230465657271220604591042285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153643771514147069727361523 230465657271220604591042285)
        ·
          refine ⟨86424621476707726721640857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230465657271220604591042285 86424621476707726721640857)
          ·
            refine ⟨64818466107530795041230643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86424621476707726721640857 64818466107530795041230643)
            ·
              refine ⟨97227699161296192561845965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64818466107530795041230643 97227699161296192561845965)
              ·
                refine ⟨36460387185486072210692237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97227699161296192561845965 36460387185486072210692237)
                ·
                  refine ⟨13672645194557277079009589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36460387185486072210692237 13672645194557277079009589)
                  ·
                    refine ⟨1281810486989744726157149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13672645194557277079009589 1281810486989744726157149)
                    ·
                      rfl

theorem cell23_7488951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_7488951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488951 prefixEnd_7488951 := by exact prefixLift 7488951
  have htrace : WordTrace (prefixWord ++ tailWord_7488951) baseStart_7488951 baseEnd_7488951 := by
    simpa [prefixWord, tailWord_7488951, baseEnd_7488951] using wordTrace_append hprefix tailTrace_7488951
  have hstable : (prefixWord ++ tailWord_7488951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488951).length < 2 ^ (prefixWord ++ tailWord_7488951).sum := by decide
  have hdescent : baseEnd_7488951 < baseStart_7488951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488968 : List Nat := [2, 1, 3, 1, 3, 1, 3, 3, 1, 5]
def baseStart_7488968 : Nat := 118140960795 + 7488968 * 2 ^ 59
def prefixEnd_7488968 : Nat := 4983230072969 + 3 ^ 40 * 7488968 * 2
def baseEnd_7488968 : Nat := 1281813396713453537319623

theorem tailTrace_7488968 : CollatzResearch.WordTrace tailWord_7488968 prefixEnd_7488968 1281813396713453537319623 := by
  unfold tailWord_7488968
  simp only [CollatzResearch.WordTrace]
  refine ⟨136572551366377712376005779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182096735155170283168007705 136572551366377712376005779)
  ·
    refine ⟨204858827049566568564008669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136572551366377712376005779 204858827049566568564008669)
    ·
      refine ⟨76822060143587463211503251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204858827049566568564008669 76822060143587463211503251)
      ·
        refine ⟨115233090215381194817254877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76822060143587463211503251 115233090215381194817254877)
        ·
          refine ⟨43212408830767948056470579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115233090215381194817254877 43212408830767948056470579)
          ·
            refine ⟨64818613246151922084705869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43212408830767948056470579 64818613246151922084705869)
            ·
              refine ⟨24306979967306970781764701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64818613246151922084705869 24306979967306970781764701)
              ·
                refine ⟨9115117487740114043161763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24306979967306970781764701 9115117487740114043161763)
                ·
                  refine ⟨13672676231610171064742645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9115117487740114043161763 13672676231610171064742645)
                  ·
                    refine ⟨1281813396713453537319623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13672676231610171064742645 1281813396713453537319623)
                    ·
                      rfl

theorem cell23_7488968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_7488968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488968 prefixEnd_7488968 := by exact prefixLift 7488968
  have htrace : WordTrace (prefixWord ++ tailWord_7488968) baseStart_7488968 baseEnd_7488968 := by
    simpa [prefixWord, tailWord_7488968, baseEnd_7488968] using wordTrace_append hprefix tailTrace_7488968
  have hstable : (prefixWord ++ tailWord_7488968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488968).length < 2 ^ (prefixWord ++ tailWord_7488968).sum := by decide
  have hdescent : baseEnd_7488968 < baseStart_7488968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7488982 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_7488982 : Nat := 118140960795 + 7488982 * 2 ^ 59
def prefixEnd_7488982 : Nat := 4983230072969 + 3 ^ 40 * 7488982 * 2
def baseEnd_7488982 : Nat := 3845447378869523557183805

theorem tailTrace_7488982 : CollatzResearch.WordTrace tailWord_7488982 prefixEnd_7488982 3845447378869523557183805 := by
  unfold tailWord_7488982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17071600834669044071438825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182097075569803136762014133 17071600834669044071438825)
  ·
    refine ⟨12803700626001783053579119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17071600834669044071438825 12803700626001783053579119)
    ·
      refine ⟨19205550939002674580368679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12803700626001783053579119 19205550939002674580368679)
      ·
        refine ⟨28808326408504011870553019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19205550939002674580368679 28808326408504011870553019)
        ·
          refine ⟨43212489612756017805829529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28808326408504011870553019 43212489612756017805829529)
          ·
            refine ⟨32409367209567013354372147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43212489612756017805829529 32409367209567013354372147)
            ·
              refine ⟨48614050814350520031558221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32409367209567013354372147 48614050814350520031558221)
              ·
                refine ⟨18230269055381445011834333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48614050814350520031558221 18230269055381445011834333)
                ·
                  refine ⟨6836350895768041879437875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18230269055381445011834333 6836350895768041879437875)
                  ·
                    refine ⟨10254526343652062819156813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6836350895768041879437875 10254526343652062819156813)
                    ·
                      refine ⟨3845447378869523557183805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10254526343652062819156813 3845447378869523557183805)
                      ·
                        rfl

theorem cell23_7488982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_7488982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7488982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7488982 prefixEnd_7488982 := by exact prefixLift 7488982
  have htrace : WordTrace (prefixWord ++ tailWord_7488982) baseStart_7488982 baseEnd_7488982 := by
    simpa [prefixWord, tailWord_7488982, baseEnd_7488982] using wordTrace_append hprefix tailTrace_7488982
  have hstable : (prefixWord ++ tailWord_7488982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7488982).length < 2 ^ (prefixWord ++ tailWord_7488982).sum := by decide
  have hdescent : baseEnd_7488982 < baseStart_7488982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7488982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489025 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_7489025 : Nat := 118140960795 + 7489025 * 2 ^ 59
def prefixEnd_7489025 : Nat := 4983230072969 + 3 ^ 40 * 7489025 * 2
def baseEnd_7489025 : Nat := 3845469458537666888946107

theorem tailTrace_7489025 : CollatzResearch.WordTrace tailWord_7489025 prefixEnd_7489025 3845469458537666888946107 := by
  unfold tailWord_7489025
  simp only [CollatzResearch.WordTrace]
  refine ⟨273147181693548923486836529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182098121129032615657891019 273147181693548923486836529)
  ·
    refine ⟨204860386270161692615127397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273147181693548923486836529 204860386270161692615127397)
    ·
      refine ⟨38411322425655317365336387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204860386270161692615127397 38411322425655317365336387)
      ·
        refine ⟨57616983638482976048004581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38411322425655317365336387 57616983638482976048004581)
        ·
          refine ⟨10803184432215558009000859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57616983638482976048004581 10803184432215558009000859)
          ·
            refine ⟨16204776648323337013501289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10803184432215558009000859 16204776648323337013501289)
            ·
              refine ⟨12153582486242502760125967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16204776648323337013501289 12153582486242502760125967)
              ·
                refine ⟨18230373729363754140188951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12153582486242502760125967 18230373729363754140188951)
                ·
                  refine ⟨27345560594045631210283427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18230373729363754140188951 27345560594045631210283427)
                  ·
                    refine ⟨41018340891068446815425141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27345560594045631210283427 41018340891068446815425141)
                    ·
                      refine ⟨3845469458537666888946107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41018340891068446815425141 3845469458537666888946107)
                      ·
                        rfl

theorem cell23_7489025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_7489025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489025 prefixEnd_7489025 := by exact prefixLift 7489025
  have htrace : WordTrace (prefixWord ++ tailWord_7489025) baseStart_7489025 baseEnd_7489025 := by
    simpa [prefixWord, tailWord_7489025, baseEnd_7489025] using wordTrace_append hprefix tailTrace_7489025
  have hstable : (prefixWord ++ tailWord_7489025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489025).length < 2 ^ (prefixWord ++ tailWord_7489025).sum := by decide
  have hdescent : baseEnd_7489025 < baseStart_7489025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489041 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 2, 7]
def baseStart_7489041 : Nat := 118140960795 + 7489041 * 2 ^ 59
def prefixEnd_7489041 : Nat := 4983230072969 + 3 ^ 40 * 7489041 * 2
def baseEnd_7489041 : Nat := 1281825891409379608782011

theorem tailTrace_7489041 : CollatzResearch.WordTrace tailWord_7489041 prefixEnd_7489041 1281825891409379608782011 := by
  unfold tailWord_7489041
  simp only [CollatzResearch.WordTrace]
  refine ⟨273147765261490958219418977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182098510174327305479612651 273147765261490958219418977)
  ·
    refine ⟨204860823946118218664564233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273147765261490958219418977 204860823946118218664564233)
    ·
      refine ⟨153645617959588663998423175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204860823946118218664564233 153645617959588663998423175)
      ·
        refine ⟨230468426939382995997634763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153645617959588663998423175 230468426939382995997634763)
        ·
          refine ⟨345702640409074493996452145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230468426939382995997634763 345702640409074493996452145)
          ·
            refine ⟨259276980306805870497339109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345702640409074493996452145 259276980306805870497339109)
            ·
              refine ⟨48614433807526100718251083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259276980306805870497339109 48614433807526100718251083)
              ·
                refine ⟨72921650711289151077376625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48614433807526100718251083 72921650711289151077376625)
                ·
                  refine ⟨54691238033466863308032469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72921650711289151077376625 54691238033466863308032469)
                  ·
                    refine ⟨1281825891409379608782011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54691238033466863308032469 1281825891409379608782011)
                    ·
                      rfl

theorem cell23_7489041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_7489041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489041 prefixEnd_7489041 := by exact prefixLift 7489041
  have htrace : WordTrace (prefixWord ++ tailWord_7489041) baseStart_7489041 baseEnd_7489041 := by
    simpa [prefixWord, tailWord_7489041, baseEnd_7489041] using wordTrace_append hprefix tailTrace_7489041
  have hstable : (prefixWord ++ tailWord_7489041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489041).length < 2 ^ (prefixWord ++ tailWord_7489041).sum := by decide
  have hdescent : baseEnd_7489041 < baseStart_7489041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489059 : List Nat := [1, 1, 1, 4, 6, 1, 1, 2, 1, 2, 3]
def baseStart_7489059 : Nat := 118140960795 + 7489059 * 2 ^ 59
def prefixEnd_7489059 : Nat := 4983230072969 + 3 ^ 40 * 7489059 * 2
def baseEnd_7489059 : Nat := 3845486916879919755920951

theorem tailTrace_7489059 : CollatzResearch.WordTrace tailWord_7489059 prefixEnd_7489059 3845486916879919755920951 := by
  unfold tailWord_7489059
  simp only [CollatzResearch.WordTrace]
  refine ⟨273148421775425747293574231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182098947850283831529049487 273148421775425747293574231)
  ·
    refine ⟨409722632663138620940361347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273148421775425747293574231 409722632663138620940361347)
    ·
      refine ⟨614583948994707931410542021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409722632663138620940361347 614583948994707931410542021)
      ·
        refine ⟨115234490436507737139476629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 614583948994707931410542021 115234490436507737139476629)
        ·
          refine ⟨5401616739211300178412967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115234490436507737139476629 5401616739211300178412967)
          ·
            refine ⟨8102425108816950267619451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401616739211300178412967 8102425108816950267619451)
            ·
              refine ⟨12153637663225425401429177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8102425108816950267619451 12153637663225425401429177)
              ·
                refine ⟨9115228247419069051071883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12153637663225425401429177 9115228247419069051071883)
                ·
                  refine ⟨13672842371128603576607825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9115228247419069051071883 13672842371128603576607825)
                  ·
                    refine ⟨10254631778346452682455869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13672842371128603576607825 10254631778346452682455869)
                    ·
                      refine ⟨3845486916879919755920951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10254631778346452682455869 3845486916879919755920951)
                      ·
                        rfl

theorem cell23_7489059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_7489059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489059 prefixEnd_7489059 := by exact prefixLift 7489059
  have htrace : WordTrace (prefixWord ++ tailWord_7489059) baseStart_7489059 baseEnd_7489059 := by
    simpa [prefixWord, tailWord_7489059, baseEnd_7489059] using wordTrace_append hprefix tailTrace_7489059
  have hstable : (prefixWord ++ tailWord_7489059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489059).length < 2 ^ (prefixWord ++ tailWord_7489059).sum := by decide
  have hdescent : baseEnd_7489059 < baseStart_7489059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489061 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_7489061 : Nat := 118140960795 + 7489061 * 2 ^ 59
def prefixEnd_7489061 : Nat := 4983230072969 + 3 ^ 40 * 7489061 * 2
def baseEnd_7489061 : Nat := 3845487943841228748095941

theorem tailTrace_7489061 : CollatzResearch.WordTrace tailWord_7489061 prefixEnd_7489061 3845487943841228748095941 := by
  unfold tailWord_7489061
  simp only [CollatzResearch.WordTrace]
  refine ⟨273148494721418501635147037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182098996480945667756764691 273148494721418501635147037)
  ·
    refine ⟨102430685520531938113180139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273148494721418501635147037 102430685520531938113180139)
    ·
      refine ⟨153646028280797907169770209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102430685520531938113180139 153646028280797907169770209)
      ·
        refine ⟨115234521210598430377327657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153646028280797907169770209 115234521210598430377327657)
        ·
          refine ⟨86425890907948822782995743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115234521210598430377327657 86425890907948822782995743)
          ·
            refine ⟨129638836361923234174493615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86425890907948822782995743 129638836361923234174493615)
            ·
              refine ⟨194458254542884851261740423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129638836361923234174493615 194458254542884851261740423)
              ·
                refine ⟨291687381814327276892610635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194458254542884851261740423 291687381814327276892610635)
                ·
                  refine ⟨437531072721490915338915953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291687381814327276892610635 437531072721490915338915953)
                  ·
                    refine ⟨328148304541118186504186965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 437531072721490915338915953 328148304541118186504186965)
                    ·
                      refine ⟨3845487943841228748095941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 328148304541118186504186965 3845487943841228748095941)
                      ·
                        rfl

theorem cell23_7489061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_7489061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489061 prefixEnd_7489061 := by exact prefixLift 7489061
  have htrace : WordTrace (prefixWord ++ tailWord_7489061) baseStart_7489061 baseEnd_7489061 := by
    simpa [prefixWord, tailWord_7489061, baseEnd_7489061] using wordTrace_append hprefix tailTrace_7489061
  have hstable : (prefixWord ++ tailWord_7489061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489061).length < 2 ^ (prefixWord ++ tailWord_7489061).sum := by decide
  have hdescent : baseEnd_7489061 < baseStart_7489061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489091 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 6]
def baseStart_7489091 : Nat := 118140960795 + 7489091 * 2 ^ 59
def prefixEnd_7489091 : Nat := 4983230072969 + 3 ^ 40 * 7489091 * 2
def baseEnd_7489091 : Nat := 3845503348260863630720803

theorem tailTrace_7489091 : CollatzResearch.WordTrace tailWord_7489091 prefixEnd_7489091 3845503348260863630720803 := by
  unfold tailWord_7489091
  simp only [CollatzResearch.WordTrace]
  refine ⟨273149588911309816758739127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182099725940873211172492751 273149588911309816758739127)
  ·
    refine ⟨409724383366964725138108691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273149588911309816758739127 409724383366964725138108691)
    ·
      refine ⟨614586575050447087707163037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409724383366964725138108691 614586575050447087707163037)
      ·
        refine ⟨230469965643917657890186139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 614586575050447087707163037 230469965643917657890186139)
        ·
          refine ⟨345704948465876486835279209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230469965643917657890186139 345704948465876486835279209)
          ·
            refine ⟨259278711349407365126459407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345704948465876486835279209 259278711349407365126459407)
            ·
              refine ⟨388918067024111047689689111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259278711349407365126459407 388918067024111047689689111)
              ·
                refine ⟨583377100536166571534533667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388918067024111047689689111 583377100536166571534533667)
                ·
                  refine ⟨875065650804249857301800501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583377100536166571534533667 875065650804249857301800501)
                  ·
                    refine ⟨82037404762898424122043797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 875065650804249857301800501 82037404762898424122043797)
                    ·
                      refine ⟨3845503348260863630720803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82037404762898424122043797 3845503348260863630720803)
                      ·
                        rfl

theorem cell23_7489091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_7489091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489091 prefixEnd_7489091 := by exact prefixLift 7489091
  have htrace : WordTrace (prefixWord ++ tailWord_7489091) baseStart_7489091 baseEnd_7489091 := by
    simpa [prefixWord, tailWord_7489091, baseEnd_7489091] using wordTrace_append hprefix tailTrace_7489091
  have hstable : (prefixWord ++ tailWord_7489091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489091).length < 2 ^ (prefixWord ++ tailWord_7489091).sum := by decide
  have hdescent : baseEnd_7489091 < baseStart_7489091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489098 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_7489098 : Nat := 118140960795 + 7489098 * 2 ^ 59
def prefixEnd_7489098 : Nat := 4983230072969 + 3 ^ 40 * 7489098 * 2
def baseEnd_7489098 : Nat := 3845506942625445103333271

theorem tailTrace_7489098 : CollatzResearch.WordTrace tailWord_7489098 prefixEnd_7489098 3845506942625445103333271 := by
  unfold tailWord_7489098
  simp only [CollatzResearch.WordTrace]
  refine ⟨68287461055571114238560987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182099896148189637969495965 68287461055571114238560987)
  ·
    refine ⟨102431191583356671357841481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68287461055571114238560987 102431191583356671357841481)
    ·
      refine ⟨76823393687517503518381111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102431191583356671357841481 76823393687517503518381111)
      ·
        refine ⟨115235090531276255277571667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76823393687517503518381111 115235090531276255277571667)
        ·
          refine ⟨172852635796914382916357501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115235090531276255277571667 172852635796914382916357501)
          ·
            refine ⟨64819738423842893593634063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172852635796914382916357501 64819738423842893593634063)
            ·
              refine ⟨97229607635764340390451095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64819738423842893593634063 97229607635764340390451095)
              ·
                refine ⟨145844411453646510585676643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97229607635764340390451095 145844411453646510585676643)
                ·
                  refine ⟨218766617180469765878514965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145844411453646510585676643 218766617180469765878514965)
                  ·
                    refine ⟨10254685180334520275555389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 218766617180469765878514965 10254685180334520275555389)
                    ·
                      refine ⟨3845506942625445103333271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10254685180334520275555389 3845506942625445103333271)
                      ·
                        rfl

theorem cell23_7489098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_7489098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489098 prefixEnd_7489098 := by exact prefixLift 7489098
  have htrace : WordTrace (prefixWord ++ tailWord_7489098) baseStart_7489098 baseEnd_7489098 := by
    simpa [prefixWord, tailWord_7489098, baseEnd_7489098] using wordTrace_append hprefix tailTrace_7489098
  have hstable : (prefixWord ++ tailWord_7489098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489098).length < 2 ^ (prefixWord ++ tailWord_7489098).sum := by decide
  have hdescent : baseEnd_7489098 < baseStart_7489098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489133 : List Nat := [1, 5, 1, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_7489133 : Nat := 118140960795 + 7489133 * 2 ^ 59
def prefixEnd_7489133 : Nat := 4983230072969 + 3 ^ 40 * 7489133 * 2
def baseEnd_7489133 : Nat := 3845524914448352466395611

theorem tailTrace_7489133 : CollatzResearch.WordTrace tailWord_7489133 prefixEnd_7489133 3845524914448352466395611 := by
  unfold tailWord_7489133
  simp only [CollatzResearch.WordTrace]
  refine ⟨273151120777157657931768053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182100747184771771954512035 273151120777157657931768053)
  ·
    refine ⟨25607917572858530431103255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273151120777157657931768053 25607917572858530431103255)
    ·
      refine ⟨38411876359287795646654883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25607917572858530431103255 38411876359287795646654883)
      ·
        refine ⟨57617814538931693469982325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38411876359287795646654883 57617814538931693469982325)
        ·
          refine ⟨5401670113024846262810843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57617814538931693469982325 5401670113024846262810843)
          ·
            refine ⟨8102505169537269394216265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401670113024846262810843 8102505169537269394216265)
            ·
              refine ⟨6076878877152952045662199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8102505169537269394216265 6076878877152952045662199)
              ·
                refine ⟨9115318315729428068493299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6076878877152952045662199 9115318315729428068493299)
                ·
                  refine ⟨13672977473594142102739949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9115318315729428068493299 13672977473594142102739949)
                  ·
                    refine ⟨5127366552597803288527481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13672977473594142102739949 5127366552597803288527481)
                    ·
                      refine ⟨3845524914448352466395611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5127366552597803288527481 3845524914448352466395611)
                      ·
                        rfl

theorem cell23_7489133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_7489133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489133 prefixEnd_7489133 := by exact prefixLift 7489133
  have htrace : WordTrace (prefixWord ++ tailWord_7489133) baseStart_7489133 baseEnd_7489133 := by
    simpa [prefixWord, tailWord_7489133, baseEnd_7489133] using wordTrace_append hprefix tailTrace_7489133
  have hstable : (prefixWord ++ tailWord_7489133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489133).length < 2 ^ (prefixWord ++ tailWord_7489133).sum := by decide
  have hdescent : baseEnd_7489133 < baseStart_7489133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489148 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 4, 5]
def baseStart_7489148 : Nat := 118140960795 + 7489148 * 2 ^ 59
def prefixEnd_7489148 : Nat := 4983230072969 + 3 ^ 40 * 7489148 * 2
def baseEnd_7489148 : Nat := 1281844205552723302569347

theorem tailTrace_7489148 : CollatzResearch.WordTrace tailWord_7489148 prefixEnd_7489148 1281844205552723302569347 := by
  unfold tailWord_7489148
  simp only [CollatzResearch.WordTrace]
  refine ⟨136575833936051657746782049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182101111914735543662376065 136575833936051657746782049)
  ·
    refine ⟨102431875452038743310086537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136575833936051657746782049 102431875452038743310086537)
    ·
      refine ⟨76823906589029057482564903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102431875452038743310086537 76823906589029057482564903)
      ·
        refine ⟨115235859883543586223847355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76823906589029057482564903 115235859883543586223847355)
        ·
          refine ⟨172853789825315379335771033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115235859883543586223847355 172853789825315379335771033)
          ·
            refine ⟨129640342368986534501828275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172853789825315379335771033 129640342368986534501828275)
            ·
              refine ⟨194460513553479801752742413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129640342368986534501828275 194460513553479801752742413)
              ·
                refine ⟨72922692582554925657278405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194460513553479801752742413 72922692582554925657278405)
                ·
                  refine ⟨13673004859229048560739701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72922692582554925657278405 13673004859229048560739701)
                  ·
                    refine ⟨1281844205552723302569347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13673004859229048560739701 1281844205552723302569347)
                    ·
                      rfl

theorem cell23_7489148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_7489148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489148 prefixEnd_7489148 := by exact prefixLift 7489148
  have htrace : WordTrace (prefixWord ++ tailWord_7489148) baseStart_7489148 baseEnd_7489148 := by
    simpa [prefixWord, tailWord_7489148, baseEnd_7489148] using wordTrace_append hprefix tailTrace_7489148
  have hstable : (prefixWord ++ tailWord_7489148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489148).length < 2 ^ (prefixWord ++ tailWord_7489148).sum := by decide
  have hdescent : baseEnd_7489148 < baseStart_7489148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489185 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_7489185 : Nat := 118140960795 + 7489185 * 2 ^ 59
def prefixEnd_7489185 : Nat := 4983230072969 + 3 ^ 40 * 7489185 * 2
def baseEnd_7489185 : Nat := 3845551615442386262945371

theorem tailTrace_7489185 : CollatzResearch.WordTrace tailWord_7489185 prefixEnd_7489185 3845551615442386262945371 := by
  unfold tailWord_7489185
  simp only [CollatzResearch.WordTrace]
  refine ⟨273153017372969270812661009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182102011581979513875107339 273153017372969270812661009)
  ·
    refine ⟨204864763029726953109495757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273153017372969270812661009 204864763029726953109495757)
    ·
      refine ⟨76824286136147607416060909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204864763029726953109495757 76824286136147607416060909)
      ·
        refine ⟨28809107301055352781022841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76824286136147607416060909 28809107301055352781022841)
        ·
          refine ⟨21606830475791514585767131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28809107301055352781022841 21606830475791514585767131)
          ·
            refine ⟨32410245713687271878650697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21606830475791514585767131 32410245713687271878650697)
            ·
              refine ⟨24307684285265453908988023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32410245713687271878650697 24307684285265453908988023)
              ·
                refine ⟨36461526427898180863482035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24307684285265453908988023 36461526427898180863482035)
                ·
                  refine ⟨54692289641847271295223053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36461526427898180863482035 54692289641847271295223053)
                  ·
                    refine ⟨20509608615692726735708645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54692289641847271295223053 20509608615692726735708645)
                    ·
                      refine ⟨3845551615442386262945371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20509608615692726735708645 3845551615442386262945371)
                      ·
                        rfl

theorem cell23_7489185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_7489185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489185 prefixEnd_7489185 := by exact prefixLift 7489185
  have htrace : WordTrace (prefixWord ++ tailWord_7489185) baseStart_7489185 baseEnd_7489185 := by
    simpa [prefixWord, tailWord_7489185, baseEnd_7489185] using wordTrace_append hprefix tailTrace_7489185
  have hstable : (prefixWord ++ tailWord_7489185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489185).length < 2 ^ (prefixWord ++ tailWord_7489185).sum := by decide
  have hdescent : baseEnd_7489185 < baseStart_7489185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489186 : List Nat := [3, 3, 1, 4, 1, 2, 1, 3, 5]
def baseStart_7489186 : Nat := 118140960795 + 7489186 * 2 ^ 59
def prefixEnd_7489186 : Nat := 4983230072969 + 3 ^ 40 * 7489186 * 2
def baseEnd_7489186 : Nat := 427283569880337862114763

theorem tailTrace_7489186 : CollatzResearch.WordTrace tailWord_7489186 prefixEnd_7489186 427283569880337862114763 := by
  unfold tailWord_7489186
  simp only [CollatzResearch.WordTrace]
  refine ⟨68288263461491411995861853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182102035897310431988964941 68288263461491411995861853)
  ·
    refine ⟨25608098798059279498448195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68288263461491411995861853 25608098798059279498448195)
    ·
      refine ⟨38412148197088919247672293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25608098798059279498448195 38412148197088919247672293)
      ·
        refine ⟨7202277786954172358938555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38412148197088919247672293 7202277786954172358938555)
        ·
          refine ⟨10803416680431258538407833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7202277786954172358938555 10803416680431258538407833)
          ·
            refine ⟨8102562510323443903805875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10803416680431258538407833 8102562510323443903805875)
            ·
              refine ⟨12153843765485165855708813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8102562510323443903805875 12153843765485165855708813)
              ·
                refine ⟨4557691412056937195890805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12153843765485165855708813 4557691412056937195890805)
                ·
                  refine ⟨427283569880337862114763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4557691412056937195890805 427283569880337862114763)
                  ·
                    rfl

theorem cell23_7489186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_7489186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489186 prefixEnd_7489186 := by exact prefixLift 7489186
  have htrace : WordTrace (prefixWord ++ tailWord_7489186) baseStart_7489186 baseEnd_7489186 := by
    simpa [prefixWord, tailWord_7489186, baseEnd_7489186] using wordTrace_append hprefix tailTrace_7489186
  have hstable : (prefixWord ++ tailWord_7489186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489186).length < 2 ^ (prefixWord ++ tailWord_7489186).sum := by decide
  have hdescent : baseEnd_7489186 < baseStart_7489186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489212 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 3, 4]
def baseStart_7489212 : Nat := 118140960795 + 7489212 * 2 ^ 59
def prefixEnd_7489212 : Nat := 4983230072969 + 3 ^ 40 * 7489212 * 2
def baseEnd_7489212 : Nat := 1281855159806685885769249

theorem tailTrace_7489212 : CollatzResearch.WordTrace tailWord_7489212 prefixEnd_7489212 1281855159806685885769249 := by
  unfold tailWord_7489212
  simp only [CollatzResearch.WordTrace]
  refine ⟨136577001071935727211946945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182102668095914302949262593 136577001071935727211946945)
  ·
    refine ⟨102432750803951795408960209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136577001071935727211946945 102432750803951795408960209)
    ·
      refine ⟨76824563102963846556720157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102432750803951795408960209 76824563102963846556720157)
      ·
        refine ⟨28809211163611442458770059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76824563102963846556720157 28809211163611442458770059)
        ·
          refine ⟨43213816745417163688155089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28809211163611442458770059 43213816745417163688155089)
          ·
            refine ⟨32410362559062872766116317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43213816745417163688155089 32410362559062872766116317)
            ·
              refine ⟨12153885959648577287293619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32410362559062872766116317 12153885959648577287293619)
              ·
                refine ⟨18230828939472865930940429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12153885959648577287293619 18230828939472865930940429)
                ·
                  refine ⟨6836560852302324724102661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18230828939472865930940429 6836560852302324724102661)
                  ·
                    refine ⟨1281855159806685885769249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6836560852302324724102661 1281855159806685885769249)
                    ·
                      rfl

theorem cell23_7489212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_7489212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489212 prefixEnd_7489212 := by exact prefixLift 7489212
  have htrace : WordTrace (prefixWord ++ tailWord_7489212) baseStart_7489212 baseEnd_7489212 := by
    simpa [prefixWord, tailWord_7489212, baseEnd_7489212] using wordTrace_append hprefix tailTrace_7489212
  have hstable : (prefixWord ++ tailWord_7489212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489212).length < 2 ^ (prefixWord ++ tailWord_7489212).sum := by decide
  have hdescent : baseEnd_7489212 < baseStart_7489212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489285 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 8, 4]
def baseStart_7489285 : Nat := 118140960795 + 7489285 * 2 ^ 59
def prefixEnd_7489285 : Nat := 4983230072969 + 3 ^ 40 * 7489285 * 2
def baseEnd_7489285 : Nat := 1281867654502611957231637

theorem tailTrace_7489285 : CollatzResearch.WordTrace tailWord_7489285 prefixEnd_7489285 1281867654502611957231637 := by
  unfold tailWord_7489285
  simp only [CollatzResearch.WordTrace]
  refine ⟨273156664672606987891301309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182104443115071325260867539 273156664672606987891301309)
  ·
    refine ⟨102433749252227620459237991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273156664672606987891301309 102433749252227620459237991)
    ·
      refine ⟨153650623878341430688856987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102433749252227620459237991 153650623878341430688856987)
      ·
        refine ⟨230475935817512146033285481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153650623878341430688856987 230475935817512146033285481)
        ·
          refine ⟨172856951863134109524964111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230475935817512146033285481 172856951863134109524964111)
          ·
            refine ⟨259285427794701164287446167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172856951863134109524964111 259285427794701164287446167)
            ·
              refine ⟨388928141692051746431169251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259285427794701164287446167 388928141692051746431169251)
              ·
                refine ⟨583392212538077619646753877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388928141692051746431169251 583392212538077619646753877)
                ·
                  refine ⟨6836627490680597105235397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 583392212538077619646753877 6836627490680597105235397)
                  ·
                    refine ⟨1281867654502611957231637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6836627490680597105235397 1281867654502611957231637)
                    ·
                      rfl

theorem cell23_7489285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_7489285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489285 prefixEnd_7489285 := by exact prefixLift 7489285
  have htrace : WordTrace (prefixWord ++ tailWord_7489285) baseStart_7489285 baseEnd_7489285 := by
    simpa [prefixWord, tailWord_7489285, baseEnd_7489285] using wordTrace_append hprefix tailTrace_7489285
  have hstable : (prefixWord ++ tailWord_7489285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489285).length < 2 ^ (prefixWord ++ tailWord_7489285).sum := by decide
  have hdescent : baseEnd_7489285 < baseStart_7489285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489369 : List Nat := [1, 2, 1, 2, 2, 3, 1, 5, 1, 3, 2]
def baseStart_7489369 : Nat := 118140960795 + 7489369 * 2 ^ 59
def prefixEnd_7489369 : Nat := 4983230072969 + 3 ^ 40 * 7489369 * 2
def baseEnd_7489369 : Nat := 3845646095882813543044525

theorem tailTrace_7489369 : CollatzResearch.WordTrace tailWord_7489369 prefixEnd_7489369 3845646095882813543044525 := by
  unfold tailWord_7489369
  simp only [CollatzResearch.WordTrace]
  refine ⟨273159728404302670237359161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182106485602868446824906107 273159728404302670237359161)
  ·
    refine ⟨204869796303227002678019371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273159728404302670237359161 204869796303227002678019371)
    ·
      refine ⟨307304694454840504017029057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204869796303227002678019371 307304694454840504017029057)
      ·
        refine ⟨230478520841130378012771793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307304694454840504017029057 230478520841130378012771793)
        ·
          refine ⟨172858890630847783509578845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230478520841130378012771793 172858890630847783509578845)
          ·
            refine ⟨64822083986567918816092067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172858890630847783509578845 64822083986567918816092067)
            ·
              refine ⟨97233125979851878224138101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64822083986567918816092067 97233125979851878224138101)
              ·
                refine ⟨9115605560611113583512947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97233125979851878224138101 9115605560611113583512947)
                ·
                  refine ⟨13673408340916670375269421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9115605560611113583512947 13673408340916670375269421)
                  ·
                    refine ⟨5127528127843751390726033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13673408340916670375269421 5127528127843751390726033)
                    ·
                      refine ⟨3845646095882813543044525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5127528127843751390726033 3845646095882813543044525)
                      ·
                        rfl

theorem cell23_7489369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 3, 2].length) (baseStart_7489369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489369 prefixEnd_7489369 := by exact prefixLift 7489369
  have htrace : WordTrace (prefixWord ++ tailWord_7489369) baseStart_7489369 baseEnd_7489369 := by
    simpa [prefixWord, tailWord_7489369, baseEnd_7489369] using wordTrace_append hprefix tailTrace_7489369
  have hstable : (prefixWord ++ tailWord_7489369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489369).length < 2 ^ (prefixWord ++ tailWord_7489369).sum := by decide
  have hdescent : baseEnd_7489369 < baseStart_7489369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489395 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 4]
def baseStart_7489395 : Nat := 118140960795 + 7489395 * 2 ^ 59
def prefixEnd_7489395 : Nat := 4983230072969 + 3 ^ 40 * 7489395 * 2
def baseEnd_7489395 : Nat := 3845659446379830441319405

theorem tailTrace_7489395 : CollatzResearch.WordTrace tailWord_7489395 prefixEnd_7489395 3845659446379830441319405 := by
  unfold tailWord_7489395
  simp only [CollatzResearch.WordTrace]
  refine ⟨273160676702208476677805639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182107117801472317785203759 273160676702208476677805639)
  ·
    refine ⟨409741015053312715016708459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273160676702208476677805639 409741015053312715016708459)
    ·
      refine ⟨614611522579969072525062689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409741015053312715016708459 614611522579969072525062689)
      ·
        refine ⟨460958641934976804393797017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614611522579969072525062689 460958641934976804393797017)
        ·
          refine ⟨345718981451232603295347763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460958641934976804393797017 345718981451232603295347763)
          ·
            refine ⟨518578472176848904943021645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345718981451232603295347763 518578472176848904943021645)
            ·
              refine ⟨194466927066318339353633117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 518578472176848904943021645 194466927066318339353633117)
              ·
                refine ⟨72925097649869377257612419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194466927066318339353633117 72925097649869377257612419)
                ·
                  refine ⟨109387646474804065886418629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72925097649869377257612419 109387646474804065886418629)
                  ·
                    refine ⟨20510183714025762353703493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109387646474804065886418629 20510183714025762353703493)
                    ·
                      refine ⟨3845659446379830441319405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20510183714025762353703493 3845659446379830441319405)
                      ·
                        rfl

theorem cell23_7489395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_7489395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489395 prefixEnd_7489395 := by exact prefixLift 7489395
  have htrace : WordTrace (prefixWord ++ tailWord_7489395) baseStart_7489395 baseEnd_7489395 := by
    simpa [prefixWord, tailWord_7489395, baseEnd_7489395] using wordTrace_append hprefix tailTrace_7489395
  have hstable : (prefixWord ++ tailWord_7489395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489395).length < 2 ^ (prefixWord ++ tailWord_7489395).sum := by decide
  have hdescent : baseEnd_7489395 < baseStart_7489395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489405 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 9]
def baseStart_7489405 : Nat := 118140960795 + 7489405 * 2 ^ 59
def prefixEnd_7489405 : Nat := 4983230072969 + 3 ^ 40 * 7489405 * 2
def baseEnd_7489405 : Nat := 427296064576263933577151

theorem tailTrace_7489405 : CollatzResearch.WordTrace tailWord_7489405 prefixEnd_7489405 427296064576263933577151 := by
  unfold tailWord_7489405
  simp only [CollatzResearch.WordTrace]
  refine ⟨273161041432172248385669669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182107360954781498923779779 273161041432172248385669669)
  ·
    refine ⟨51217695268532296572313063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273161041432172248385669669 51217695268532296572313063)
    ·
      refine ⟨76826542902798444858469595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51217695268532296572313063 76826542902798444858469595)
      ·
        refine ⟨115239814354197667287704393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76826542902798444858469595 115239814354197667287704393)
        ·
          refine ⟨86429860765648250465778295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115239814354197667287704393 86429860765648250465778295)
          ·
            refine ⟨129644791148472375698667443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86429860765648250465778295 129644791148472375698667443)
            ·
              refine ⟨194467186722708563548001165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129644791148472375698667443 194467186722708563548001165)
              ·
                refine ⟨72925195021015711330500437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194467186722708563548001165 72925195021015711330500437)
                ·
                  refine ⟨427296064576263933577151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72925195021015711330500437 427296064576263933577151)
                  ·
                    rfl

theorem cell23_7489405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_7489405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489405 prefixEnd_7489405 := by exact prefixLift 7489405
  have htrace : WordTrace (prefixWord ++ tailWord_7489405) baseStart_7489405 baseEnd_7489405 := by
    simpa [prefixWord, tailWord_7489405, baseEnd_7489405] using wordTrace_append hprefix tailTrace_7489405
  have hstable : (prefixWord ++ tailWord_7489405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489405).length < 2 ^ (prefixWord ++ tailWord_7489405).sum := by decide
  have hdescent : baseEnd_7489405 < baseStart_7489405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489416 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 1, 4, 2]
def baseStart_7489416 : Nat := 118140960795 + 7489416 * 2 ^ 59
def prefixEnd_7489416 : Nat := 4983230072969 + 3 ^ 40 * 7489416 * 2
def baseEnd_7489416 : Nat := 3845670229473574859156809

theorem tailTrace_7489416 : CollatzResearch.WordTrace tailWord_7489416 prefixEnd_7489416 3845670229473574859156809 := by
  unfold tailWord_7489416
  simp only [CollatzResearch.WordTrace]
  refine ⟨136580721317566198632160051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182107628423421598176213401 136580721317566198632160051)
  ·
    refine ⟨204871081976349297948240077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136580721317566198632160051 204871081976349297948240077)
    ·
      refine ⟨76826655741130986730590029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204871081976349297948240077 76826655741130986730590029)
      ·
        refine ⟨28809995902924120023971261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76826655741130986730590029 28809995902924120023971261)
        ·
          refine ⟨10803748463596545008989223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28809995902924120023971261 10803748463596545008989223)
          ·
            refine ⟨16205622695394817513483835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10803748463596545008989223 16205622695394817513483835)
            ·
              refine ⟨24308434043092226270225753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16205622695394817513483835 24308434043092226270225753)
              ·
                refine ⟨18231325532319169702669315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24308434043092226270225753 18231325532319169702669315)
                ·
                  refine ⟨27346988298478754554003973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18231325532319169702669315 27346988298478754554003973)
                  ·
                    refine ⟨5127560305964766478875745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27346988298478754554003973 5127560305964766478875745)
                    ·
                      refine ⟨3845670229473574859156809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5127560305964766478875745 3845670229473574859156809)
                      ·
                        rfl

theorem cell23_7489416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_7489416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489416 prefixEnd_7489416 := by exact prefixLift 7489416
  have htrace : WordTrace (prefixWord ++ tailWord_7489416) baseStart_7489416 baseEnd_7489416 := by
    simpa [prefixWord, tailWord_7489416, baseEnd_7489416] using wordTrace_append hprefix tailTrace_7489416
  have hstable : (prefixWord ++ tailWord_7489416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489416).length < 2 ^ (prefixWord ++ tailWord_7489416).sum := by decide
  have hdescent : baseEnd_7489416 < baseStart_7489416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489469 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_7489469 : Nat := 118140960795 + 7489469 * 2 ^ 59
def prefixEnd_7489469 : Nat := 4983230072969 + 3 ^ 40 * 7489469 * 2
def baseEnd_7489469 : Nat := 1281899147982754383931355

theorem tailTrace_7489469 : CollatzResearch.WordTrace tailWord_7489469 prefixEnd_7489469 1281899147982754383931355 := by
  unfold tailWord_7489469
  simp only [CollatzResearch.WordTrace]
  refine ⟨273163375703940387315999461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182108917135960258210666307 273163375703940387315999461)
  ·
    refine ⟨51218132944488822621749899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273163375703940387315999461 51218132944488822621749899)
    ·
      refine ⟨76827199416733233932624849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51218132944488822621749899 76827199416733233932624849)
      ·
        refine ⟨57620399562549925449468637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76827199416733233932624849 57620399562549925449468637)
        ·
          refine ⟨21607649835956222043550739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57620399562549925449468637 21607649835956222043550739)
          ·
            refine ⟨32411474753934333065326109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21607649835956222043550739 32411474753934333065326109)
            ·
              refine ⟨12154303032725374899497291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32411474753934333065326109 12154303032725374899497291)
              ·
                refine ⟨18231454549088062349245937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12154303032725374899497291 18231454549088062349245937)
                ·
                  refine ⟨13673590911816046761934453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18231454549088062349245937 13673590911816046761934453)
                  ·
                    refine ⟨1281899147982754383931355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13673590911816046761934453 1281899147982754383931355)
                    ·
                      rfl

theorem cell23_7489469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_7489469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489469 prefixEnd_7489469 := by exact prefixLift 7489469
  have htrace : WordTrace (prefixWord ++ tailWord_7489469) baseStart_7489469 baseEnd_7489469 := by
    simpa [prefixWord, tailWord_7489469, baseEnd_7489469] using wordTrace_append hprefix tailTrace_7489469
  have hstable : (prefixWord ++ tailWord_7489469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489469).length < 2 ^ (prefixWord ++ tailWord_7489469).sum := by decide
  have hdescent : baseEnd_7489469 < baseStart_7489469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489472 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 4]
def baseStart_7489472 : Nat := 118140960795 + 7489472 * 2 ^ 59
def prefixEnd_7489472 : Nat := 4983230072969 + 3 ^ 40 * 7489472 * 2
def baseEnd_7489472 : Nat := 3845698984390226640056551

theorem tailTrace_7489472 : CollatzResearch.WordTrace tailWord_7489472 prefixEnd_7489472 3845698984390226640056551 := by
  unfold tailWord_7489472
  simp only [CollatzResearch.WordTrace]
  refine ⟨136581742561464759414179335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182108990081953012552239113 136581742561464759414179335)
  ·
    refine ⟨204872613842197139121269003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136581742561464759414179335 204872613842197139121269003)
    ·
      refine ⟨307308920763295708681903505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204872613842197139121269003 307308920763295708681903505)
      ·
        refine ⟨230481690572471781511427629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307308920763295708681903505 230481690572471781511427629)
        ·
          refine ⟨86430633964676918066785361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230481690572471781511427629 86430633964676918066785361)
          ·
            refine ⟨64822975473507688550089021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86430633964676918066785361 64822975473507688550089021)
            ·
              refine ⟨24308615802565383206283383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64822975473507688550089021 24308615802565383206283383)
              ·
                refine ⟨36462923703848074809425075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24308615802565383206283383 36462923703848074809425075)
                ·
                  refine ⟨54694385555772112214137613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36462923703848074809425075 54694385555772112214137613)
                  ·
                    refine ⟨20510394583414542080301605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54694385555772112214137613 20510394583414542080301605)
                    ·
                      refine ⟨3845698984390226640056551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20510394583414542080301605 3845698984390226640056551)
                      ·
                        rfl

theorem cell23_7489472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_7489472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489472 prefixEnd_7489472 := by exact prefixLift 7489472
  have htrace : WordTrace (prefixWord ++ tailWord_7489472) baseStart_7489472 baseEnd_7489472 := by
    simpa [prefixWord, tailWord_7489472, baseEnd_7489472] using wordTrace_append hprefix tailTrace_7489472
  have hstable : (prefixWord ++ tailWord_7489472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489472).length < 2 ^ (prefixWord ++ tailWord_7489472).sum := by decide
  have hdescent : baseEnd_7489472 < baseStart_7489472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489475 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 9]
def baseStart_7489475 : Nat := 118140960795 + 7489475 * 2 ^ 59
def prefixEnd_7489475 : Nat := 4983230072969 + 3 ^ 40 * 7489475 * 2
def baseEnd_7489475 : Nat := 3845700524832190128319037

theorem tailTrace_7489475 : CollatzResearch.WordTrace tailWord_7489475 prefixEnd_7489475 3845700524832190128319037 := by
  unfold tailWord_7489475
  simp only [CollatzResearch.WordTrace]
  refine ⟨273163594541918650340717879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182109063027945766893811919 273163594541918650340717879)
  ·
    refine ⟨409745391812877975511076819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273163594541918650340717879 409745391812877975511076819)
    ·
      refine ⟨614618087719316963266615229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409745391812877975511076819 614618087719316963266615229)
      ·
        refine ⟨230481782894743861224980711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 614618087719316963266615229 230481782894743861224980711)
        ·
          refine ⟨345722674342115791837471067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230481782894743861224980711 345722674342115791837471067)
          ·
            refine ⟨518584011513173687756206601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345722674342115791837471067 518584011513173687756206601)
            ·
              refine ⟨388938008634880265817154951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518584011513173687756206601 388938008634880265817154951)
              ·
                refine ⟨583407012952320398725732427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388938008634880265817154951 583407012952320398725732427)
                ·
                  refine ⟨875110519428480598088598641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583407012952320398725732427 875110519428480598088598641)
                  ·
                    refine ⟨656332889571360448566448981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 875110519428480598088598641 656332889571360448566448981)
                    ·
                      refine ⟨3845700524832190128319037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 656332889571360448566448981 3845700524832190128319037)
                      ·
                        rfl

theorem cell23_7489475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_7489475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489475 prefixEnd_7489475 := by exact prefixLift 7489475
  have htrace : WordTrace (prefixWord ++ tailWord_7489475) baseStart_7489475 baseEnd_7489475 := by
    simpa [prefixWord, tailWord_7489475, baseEnd_7489475] using wordTrace_append hprefix tailTrace_7489475
  have hstable : (prefixWord ++ tailWord_7489475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489475).length < 2 ^ (prefixWord ++ tailWord_7489475).sum := by decide
  have hdescent : baseEnd_7489475 < baseStart_7489475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489539 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 5, 1, 3]
def baseStart_7489539 : Nat := 118140960795 + 7489539 * 2 ^ 59
def prefixEnd_7489539 : Nat := 4983230072969 + 3 ^ 40 * 7489539 * 2
def baseEnd_7489539 : Nat := 3845733387594077877918743

theorem tailTrace_7489539 : CollatzResearch.WordTrace tailWord_7489539 prefixEnd_7489539 3845733387594077877918743 := by
  unfold tailWord_7489539
  simp only [CollatzResearch.WordTrace]
  refine ⟨273165928813686789271047671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182110619209124526180698447 273165928813686789271047671)
  ·
    refine ⟨409748893220530183906571507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273165928813686789271047671 409748893220530183906571507)
    ·
      refine ⟨614623339830795275859857261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409748893220530183906571507 614623339830795275859857261)
      ·
        refine ⟨230483752436548228447446473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 614623339830795275859857261 230483752436548228447446473)
        ·
          refine ⟨172862814327411171335584855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230483752436548228447446473 172862814327411171335584855)
          ·
            refine ⟨259294221491116757003377283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172862814327411171335584855 259294221491116757003377283)
            ·
              refine ⟨388941332236675135505065925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259294221491116757003377283 388941332236675135505065925)
              ·
                refine ⟨72926499794376587907199861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388941332236675135505065925 72926499794376587907199861)
                ·
                  refine ⟨6836859355722805116299987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72926499794376587907199861 6836859355722805116299987)
                  ·
                    refine ⟨10255289033584207674449981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6836859355722805116299987 10255289033584207674449981)
                    ·
                      refine ⟨3845733387594077877918743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10255289033584207674449981 3845733387594077877918743)
                      ·
                        rfl

theorem cell23_7489539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_7489539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489539 prefixEnd_7489539 := by exact prefixLift 7489539
  have htrace : WordTrace (prefixWord ++ tailWord_7489539) baseStart_7489539 baseEnd_7489539 := by
    simpa [prefixWord, tailWord_7489539, baseEnd_7489539] using wordTrace_append hprefix tailTrace_7489539
  have hstable : (prefixWord ++ tailWord_7489539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489539).length < 2 ^ (prefixWord ++ tailWord_7489539).sum := by decide
  have hdescent : baseEnd_7489539 < baseStart_7489539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489579 : List Nat := [1, 1, 1, 1, 2, 1, 4, 6, 1, 1, 4]
def baseStart_7489579 : Nat := 118140960795 + 7489579 * 2 ^ 59
def prefixEnd_7489579 : Nat := 4983230072969 + 3 ^ 40 * 7489579 * 2
def baseEnd_7489579 : Nat := 3845753926820257721418559

theorem tailTrace_7489579 : CollatzResearch.WordTrace tailWord_7489579 prefixEnd_7489579 3845753926820257721418559 := by
  unfold tailWord_7489579
  simp only [CollatzResearch.WordTrace]
  refine ⟨273167387733541876102503791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182111591822361250735002527 273167387733541876102503791)
  ·
    refine ⟨409751081600312814153755687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273167387733541876102503791 409751081600312814153755687)
    ·
      refine ⟨614626622400469221230633531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409751081600312814153755687 614626622400469221230633531)
      ·
        refine ⟨921939933600703831845950297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614626622400469221230633531 921939933600703831845950297)
        ·
          refine ⟨691454950200527873884462723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921939933600703831845950297 691454950200527873884462723)
          ·
            refine ⟨1037182425300791810826694085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691454950200527873884462723 1037182425300791810826694085)
            ·
              refine ⟨194471704743898464530005141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1037182425300791810826694085 194471704743898464530005141)
              ·
                refine ⟨9115861159870240524843991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194471704743898464530005141 9115861159870240524843991)
                ·
                  refine ⟨13673791739805360787265987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9115861159870240524843991 13673791739805360787265987)
                  ·
                    refine ⟨20510687609708041180898981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13673791739805360787265987 20510687609708041180898981)
                    ·
                      refine ⟨3845753926820257721418559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20510687609708041180898981 3845753926820257721418559)
                      ·
                        rfl

theorem cell23_7489579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 1, 4].length) (baseStart_7489579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489579 prefixEnd_7489579 := by exact prefixLift 7489579
  have htrace : WordTrace (prefixWord ++ tailWord_7489579) baseStart_7489579 baseEnd_7489579 := by
    simpa [prefixWord, tailWord_7489579, baseEnd_7489579] using wordTrace_append hprefix tailTrace_7489579
  have hstable : (prefixWord ++ tailWord_7489579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489579).length < 2 ^ (prefixWord ++ tailWord_7489579).sum := by decide
  have hdescent : baseEnd_7489579 < baseStart_7489579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489589 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 6, 4]
def baseStart_7489589 : Nat := 118140960795 + 7489589 * 2 ^ 59
def prefixEnd_7489589 : Nat := 4983230072969 + 3 ^ 40 * 7489589 * 2
def baseEnd_7489589 : Nat := 1281919687208934227431171

theorem tailTrace_7489589 : CollatzResearch.WordTrace tailWord_7489589 prefixEnd_7489589 1281919687208934227431171 := by
  unfold tailWord_7489589
  simp only [CollatzResearch.WordTrace]
  refine ⟨273167752463505647810367821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182111834975670431873578547 273167752463505647810367821)
  ·
    refine ⟨102437907173814617928887933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273167752463505647810367821 102437907173814617928887933)
    ·
      refine ⟨38414215190180481723332975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102437907173814617928887933 38414215190180481723332975)
      ·
        refine ⟨57621322785270722584999463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38414215190180481723332975 57621322785270722584999463)
        ·
          refine ⟨86431984177906083877499195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57621322785270722584999463 86431984177906083877499195)
          ·
            refine ⟨129647976266859125816248793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86431984177906083877499195 129647976266859125816248793)
            ·
              refine ⟨97235982200144344362186595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129647976266859125816248793 97235982200144344362186595)
              ·
                refine ⟨145853973300216516543279893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97235982200144344362186595 145853973300216516543279893)
                ·
                  refine ⟨6836904998447649212966245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145853973300216516543279893 6836904998447649212966245)
                  ·
                    refine ⟨1281919687208934227431171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6836904998447649212966245 1281919687208934227431171)
                    ·
                      rfl

theorem cell23_7489589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_7489589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489589 prefixEnd_7489589 := by exact prefixLift 7489589
  have htrace : WordTrace (prefixWord ++ tailWord_7489589) baseStart_7489589 baseEnd_7489589 := by
    simpa [prefixWord, tailWord_7489589, baseEnd_7489589] using wordTrace_append hprefix tailTrace_7489589
  have hstable : (prefixWord ++ tailWord_7489589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489589).length < 2 ^ (prefixWord ++ tailWord_7489589).sum := by decide
  have hdescent : baseEnd_7489589 < baseStart_7489589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489590 : List Nat := [5, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_7489590 : Nat := 118140960795 + 7489590 * 2 ^ 59
def prefixEnd_7489590 : Nat := 4983230072969 + 3 ^ 40 * 7489590 * 2
def baseEnd_7489590 : Nat := 3845759575107457178381009

theorem tailTrace_7489590 : CollatzResearch.WordTrace tailWord_7489590 prefixEnd_7489590 3845759575107457178381009 := by
  unfold tailWord_7489590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17072986808531376561322139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182111859291001349987436149 17072986808531376561322139)
  ·
    refine ⟨25609480212797064841983209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17072986808531376561322139 25609480212797064841983209)
    ·
      refine ⟨19207110159597798631487407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25609480212797064841983209 19207110159597798631487407)
      ·
        refine ⟨28810665239396697947231111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19207110159597798631487407 28810665239396697947231111)
        ·
          refine ⟨43215997859095046920846667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28810665239396697947231111 43215997859095046920846667)
          ·
            refine ⟨64823996788642570381270001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43215997859095046920846667 64823996788642570381270001)
            ·
              refine ⟨48617997591481927785952501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64823996788642570381270001 48617997591481927785952501)
              ·
                refine ⟨4557937274201430729933047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48617997591481927785952501 4557937274201430729933047)
                ·
                  refine ⟨6836905911302146094899571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4557937274201430729933047 6836905911302146094899571)
                  ·
                    refine ⟨10255358866953219142349357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6836905911302146094899571 10255358866953219142349357)
                    ·
                      refine ⟨3845759575107457178381009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10255358866953219142349357 3845759575107457178381009)
                      ·
                        rfl

theorem cell23_7489590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_7489590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489590 prefixEnd_7489590 := by exact prefixLift 7489590
  have htrace : WordTrace (prefixWord ++ tailWord_7489590) baseStart_7489590 baseEnd_7489590 := by
    simpa [prefixWord, tailWord_7489590, baseEnd_7489590] using wordTrace_append hprefix tailTrace_7489590
  have hstable : (prefixWord ++ tailWord_7489590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489590).length < 2 ^ (prefixWord ++ tailWord_7489590).sum := by decide
  have hdescent : baseEnd_7489590 < baseStart_7489590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489593 : List Nat := [1, 2, 1, 5, 3, 1, 3, 1, 1, 5]
def baseStart_7489593 : Nat := 118140960795 + 7489593 * 2 ^ 59
def prefixEnd_7489593 : Nat := 4983230072969 + 3 ^ 40 * 7489593 * 2
def baseEnd_7489593 : Nat := 1281920371849806888881165

theorem tailTrace_7489593 : CollatzResearch.WordTrace tailWord_7489593 prefixEnd_7489593 1281920371849806888881165 := by
  unfold tailWord_7489593
  simp only [CollatzResearch.WordTrace]
  refine ⟨273167898355491156493513433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182111932236994104329008955 273167898355491156493513433)
  ·
    refine ⟨204875923766618367370135075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273167898355491156493513433 204875923766618367370135075)
    ·
      refine ⟨307313885649927551055202613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204875923766618367370135075 307313885649927551055202613)
      ·
        refine ⟨28810676779680707911425245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 307313885649927551055202613 28810676779680707911425245)
        ·
          refine ⟨10804003792380265466784467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28810676779680707911425245 10804003792380265466784467)
          ·
            refine ⟨16206005688570398200176701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10804003792380265466784467 16206005688570398200176701)
            ·
              refine ⟨6077252133213899325066263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16206005688570398200176701 6077252133213899325066263)
              ·
                refine ⟨9115878199820848987599395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6077252133213899325066263 9115878199820848987599395)
                ·
                  refine ⟨13673817299731273481399093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9115878199820848987599395 13673817299731273481399093)
                  ·
                    refine ⟨1281920371849806888881165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13673817299731273481399093 1281920371849806888881165)
                    ·
                      rfl

theorem cell23_7489593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 1, 5].length) (baseStart_7489593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489593 prefixEnd_7489593 := by exact prefixLift 7489593
  have htrace : WordTrace (prefixWord ++ tailWord_7489593) baseStart_7489593 baseEnd_7489593 := by
    simpa [prefixWord, tailWord_7489593, baseEnd_7489593] using wordTrace_append hprefix tailTrace_7489593
  have hstable : (prefixWord ++ tailWord_7489593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489593).length < 2 ^ (prefixWord ++ tailWord_7489593).sum := by decide
  have hdescent : baseEnd_7489593 < baseStart_7489593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489599 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 5]
def baseStart_7489599 : Nat := 118140960795 + 7489599 * 2 ^ 59
def prefixEnd_7489599 : Nat := 4983230072969 + 3 ^ 40 * 7489599 * 2
def baseEnd_7489599 : Nat := 3845764196433347643168467

theorem tailTrace_7489599 : CollatzResearch.WordTrace tailWord_7489599 prefixEnd_7489599 3845764196433347643168467 := by
  unfold tailWord_7489599
  simp only [CollatzResearch.WordTrace]
  refine ⟨273168117193469419518231851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182112078128979613012154567 273168117193469419518231851)
  ·
    refine ⟨409752175790204129277347777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273168117193469419518231851 409752175790204129277347777)
    ·
      refine ⟨307314131842653096958010833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409752175790204129277347777 307314131842653096958010833)
      ·
        refine ⟨230485598881989822718508125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307314131842653096958010833 230485598881989822718508125)
        ·
          refine ⟨86432099580746183519440547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230485598881989822718508125 86432099580746183519440547)
          ·
            refine ⟨129648149371119275279160821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86432099580746183519440547 129648149371119275279160821)
            ·
              refine ⟨12154514003542432057421327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129648149371119275279160821 12154514003542432057421327)
              ·
                refine ⟨18231771005313648086131991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12154514003542432057421327 18231771005313648086131991)
                ·
                  refine ⟨27347656507970472129197987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18231771005313648086131991 27347656507970472129197987)
                  ·
                    refine ⟨41021484761955708193796981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27347656507970472129197987 41021484761955708193796981)
                    ·
                      refine ⟨3845764196433347643168467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41021484761955708193796981 3845764196433347643168467)
                      ·
                        rfl

theorem cell23_7489599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_7489599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489599 prefixEnd_7489599 := by exact prefixLift 7489599
  have htrace : WordTrace (prefixWord ++ tailWord_7489599) baseStart_7489599 baseEnd_7489599 := by
    simpa [prefixWord, tailWord_7489599, baseEnd_7489599] using wordTrace_append hprefix tailTrace_7489599
  have hstable : (prefixWord ++ tailWord_7489599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489599).length < 2 ^ (prefixWord ++ tailWord_7489599).sum := by decide
  have hdescent : baseEnd_7489599 < baseStart_7489599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489606 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_7489606 : Nat := 118140960795 + 7489606 * 2 ^ 59
def prefixEnd_7489606 : Nat := 4983230072969 + 3 ^ 40 * 7489606 * 2
def baseEnd_7489606 : Nat := 1281922596932643038593645

theorem tailTrace_7489606 : CollatzResearch.WordTrace tailWord_7489606 prefixEnd_7489606 1281922596932643038593645 := by
  unfold tailWord_7489606
  simp only [CollatzResearch.WordTrace]
  refine ⟨8536511640763876866054271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182112248336296039809157781 8536511640763876866054271)
  ·
    refine ⟨12804767461145815299081407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8536511640763876866054271 12804767461145815299081407)
    ·
      refine ⟨19207151191718722948622111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12804767461145815299081407 19207151191718722948622111)
      ·
        refine ⟨28810726787578084422933167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19207151191718722948622111 28810726787578084422933167)
        ·
          refine ⟨43216090181367126634399751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28810726787578084422933167 43216090181367126634399751)
          ·
            refine ⟨64824135272050689951599627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43216090181367126634399751 64824135272050689951599627)
            ·
              refine ⟨97236202908076034927399441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64824135272050689951599627 97236202908076034927399441)
              ·
                refine ⟨72927152181057026195549581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97236202908076034927399441 72927152181057026195549581)
                ·
                  refine ⟨27347682067896384823331093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72927152181057026195549581 27347682067896384823331093)
                  ·
                    refine ⟨1281922596932643038593645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27347682067896384823331093 1281922596932643038593645)
                    ·
                      rfl

theorem cell23_7489606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_7489606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489606 prefixEnd_7489606 := by exact prefixLift 7489606
  have htrace : WordTrace (prefixWord ++ tailWord_7489606) baseStart_7489606 baseEnd_7489606 := by
    simpa [prefixWord, tailWord_7489606, baseEnd_7489606] using wordTrace_append hprefix tailTrace_7489606
  have hstable : (prefixWord ++ tailWord_7489606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489606).length < 2 ^ (prefixWord ++ tailWord_7489606).sum := by decide
  have hdescent : baseEnd_7489606 < baseStart_7489606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489646 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_7489646 : Nat := 118140960795 + 7489646 * 2 ^ 59
def prefixEnd_7489646 : Nat := 4983230072969 + 3 ^ 40 * 7489646 * 2
def baseEnd_7489646 : Nat := 3845788330024108959280751

theorem tailTrace_7489646 : CollatzResearch.WordTrace tailWord_7489646 prefixEnd_7489646 3845788330024108959280751 := by
  unfold tailWord_7489646
  simp only [CollatzResearch.WordTrace]
  refine ⟨34146228928037393318149099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182113220949532764363461861 34146228928037393318149099)
  ·
    refine ⟨51219343392056089977223649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34146228928037393318149099 51219343392056089977223649)
    ·
      refine ⟨38414507544042067482917737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51219343392056089977223649 38414507544042067482917737)
      ·
        refine ⟨28810880658031550612188303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38414507544042067482917737 28810880658031550612188303)
        ·
          refine ⟨43216320987047325918282455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28810880658031550612188303 43216320987047325918282455)
          ·
            refine ⟨64824481480570988877423683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43216320987047325918282455 64824481480570988877423683)
            ·
              refine ⟨97236722220856483316135525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64824481480570988877423683 97236722220856483316135525)
              ·
                refine ⟨18231885416410590621775411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97236722220856483316135525 18231885416410590621775411)
                ·
                  refine ⟨27347828124615885932663117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18231885416410590621775411 27347828124615885932663117)
                  ·
                    refine ⟨10255435546730957224748669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27347828124615885932663117 10255435546730957224748669)
                    ·
                      refine ⟨3845788330024108959280751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10255435546730957224748669 3845788330024108959280751)
                      ·
                        rfl

theorem cell23_7489646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_7489646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489646 prefixEnd_7489646 := by exact prefixLift 7489646
  have htrace : WordTrace (prefixWord ++ tailWord_7489646) baseStart_7489646 baseEnd_7489646 := by
    simpa [prefixWord, tailWord_7489646, baseEnd_7489646] using wordTrace_append hprefix tailTrace_7489646
  have hstable : (prefixWord ++ tailWord_7489646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489646).length < 2 ^ (prefixWord ++ tailWord_7489646).sum := by decide
  have hdescent : baseEnd_7489646 < baseStart_7489646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489650 : List Nat := [3, 2, 1, 2, 2, 4, 2, 1, 1, 2, 3]
def baseStart_7489650 : Nat := 118140960795 + 7489650 * 2 ^ 59
def prefixEnd_7489650 : Nat := 4983230072969 + 3 ^ 40 * 7489650 * 2
def baseEnd_7489650 : Nat := 3845790383946726943630733

theorem tailTrace_7489650 : CollatzResearch.WordTrace tailWord_7489650 prefixEnd_7489650 3845790383946726943630733 := by
  unfold tailWord_7489650
  simp only [CollatzResearch.WordTrace]
  refine ⟨68292494329071163807084601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182113318210856436818892269 68292494329071163807084601)
  ·
    refine ⟨51219370746803372855313451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68292494329071163807084601 51219370746803372855313451)
    ·
      refine ⟨76829056120205059282970177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51219370746803372855313451 76829056120205059282970177)
      ·
        refine ⟨57621792090153794462227633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76829056120205059282970177 57621792090153794462227633)
        ·
          refine ⟨43216344067615345846670725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57621792090153794462227633 43216344067615345846670725)
          ·
            refine ⟨8103064512677877346250761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43216344067615345846670725 8103064512677877346250761)
            ·
              refine ⟨6077298384508408009688071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8103064512677877346250761 6077298384508408009688071)
              ·
                refine ⟨9115947576762612014532107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6077298384508408009688071 9115947576762612014532107)
                ·
                  refine ⟨13673921365143918021798161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9115947576762612014532107 13673921365143918021798161)
                  ·
                    refine ⟨10255441023857938516348621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13673921365143918021798161 10255441023857938516348621)
                    ·
                      refine ⟨3845790383946726943630733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10255441023857938516348621 3845790383946726943630733)
                      ·
                        rfl

theorem cell23_7489650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_7489650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489650 prefixEnd_7489650 := by exact prefixLift 7489650
  have htrace : WordTrace (prefixWord ++ tailWord_7489650) baseStart_7489650 baseEnd_7489650 := by
    simpa [prefixWord, tailWord_7489650, baseEnd_7489650] using wordTrace_append hprefix tailTrace_7489650
  have hstable : (prefixWord ++ tailWord_7489650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489650).length < 2 ^ (prefixWord ++ tailWord_7489650).sum := by decide
  have hdescent : baseEnd_7489650 < baseStart_7489650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489689 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 2, 4, 3]
def baseStart_7489689 : Nat := 118140960795 + 7489689 * 2 ^ 59
def prefixEnd_7489689 : Nat := 4983230072969 + 3 ^ 40 * 7489689 * 2
def baseEnd_7489689 : Nat := 3845810409692252291043053

theorem tailTrace_7489689 : CollatzResearch.WordTrace tailWord_7489689 prefixEnd_7489689 3845810409692252291043053 := by
  unfold tailWord_7489689
  simp only [CollatzResearch.WordTrace]
  refine ⟨273171399763143364889008121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182114266508762243259338747 273171399763143364889008121)
  ·
    refine ⟨204878549822357523666756091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273171399763143364889008121 204878549822357523666756091)
    ·
      refine ⟨307317824733536285500134137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204878549822357523666756091 307317824733536285500134137)
      ·
        refine ⟨230488368550152214125100603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307317824733536285500134137 230488368550152214125100603)
        ·
          refine ⟨345732552825228321187650905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230488368550152214125100603 345732552825228321187650905)
          ·
            refine ⟨259299414618921240890738179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345732552825228321187650905 259299414618921240890738179)
            ·
              refine ⟨388949121928381861336107269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259299414618921240890738179 388949121928381861336107269)
              ·
                refine ⟨72927960361571599000520113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388949121928381861336107269 72927960361571599000520113)
                ·
                  refine ⟨54695970271178699250390085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72927960361571599000520113 54695970271178699250390085)
                  ·
                    refine ⟨10255494425846006109448141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54695970271178699250390085 10255494425846006109448141)
                    ·
                      refine ⟨3845810409692252291043053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10255494425846006109448141 3845810409692252291043053)
                      ·
                        rfl

theorem cell23_7489689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_7489689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489689 prefixEnd_7489689 := by exact prefixLift 7489689
  have htrace : WordTrace (prefixWord ++ tailWord_7489689) baseStart_7489689 baseEnd_7489689 := by
    simpa [prefixWord, tailWord_7489689, baseEnd_7489689] using wordTrace_append hprefix tailTrace_7489689
  have hstable : (prefixWord ++ tailWord_7489689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489689).length < 2 ^ (prefixWord ++ tailWord_7489689).sum := by decide
  have hdescent : baseEnd_7489689 < baseStart_7489689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489739 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 4, 5]
def baseStart_7489739 : Nat := 118140960795 + 7489739 * 2 ^ 59
def prefixEnd_7489739 : Nat := 4983230072969 + 3 ^ 40 * 7489739 * 2
def baseEnd_7489739 : Nat := 1281945361241659031805941

theorem tailTrace_7489739 : CollatzResearch.WordTrace tailWord_7489739 prefixEnd_7489739 1281945361241659031805941 := by
  unfold tailWord_7489739
  simp only [CollatzResearch.WordTrace]
  refine ⟨273173223412962223428328271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182115482275308148952218847 273173223412962223428328271)
  ·
    refine ⟨409759835119443335142492407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273173223412962223428328271 409759835119443335142492407)
    ·
      refine ⟨614639752679165002713738611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409759835119443335142492407 614639752679165002713738611)
      ·
        refine ⟨921959629018747504070607917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614639752679165002713738611 921959629018747504070607917)
        ·
          refine ⟨345734860882030314026477969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 921959629018747504070607917 345734860882030314026477969)
          ·
            refine ⟨259301145661522735519858477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345734860882030314026477969 259301145661522735519858477)
            ·
              refine ⟨97237929623071025819946929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259301145661522735519858477 97237929623071025819946929)
              ·
                refine ⟨72928447217303269364960197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97237929623071025819946929 72928447217303269364960197)
                ·
                  refine ⟨13674083853244363005930037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72928447217303269364960197 13674083853244363005930037)
                  ·
                    refine ⟨1281945361241659031805941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13674083853244363005930037 1281945361241659031805941)
                    ·
                      rfl

theorem cell23_7489739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 5].length) (baseStart_7489739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489739 prefixEnd_7489739 := by exact prefixLift 7489739
  have htrace : WordTrace (prefixWord ++ tailWord_7489739) baseStart_7489739 baseEnd_7489739 := by
    simpa [prefixWord, tailWord_7489739, baseEnd_7489739] using wordTrace_append hprefix tailTrace_7489739
  have hstable : (prefixWord ++ tailWord_7489739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489739).length < 2 ^ (prefixWord ++ tailWord_7489739).sum := by decide
  have hdescent : baseEnd_7489739 < baseStart_7489739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489776 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 3, 6, 2]
def baseStart_7489776 : Nat := 118140960795 + 7489776 * 2 ^ 59
def prefixEnd_7489776 : Nat := 4983230072969 + 3 ^ 40 * 7489776 * 2
def baseEnd_7489776 : Nat := 3845855082509193450655153

theorem tailTrace_7489776 : CollatzResearch.WordTrace tailWord_7489776 prefixEnd_7489776 3845855082509193450655153 := by
  unfold tailWord_7489776
  simp only [CollatzResearch.WordTrace]
  refine ⟨136587286456914089373712591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182116381942552119164950121 136587286456914089373712591)
  ·
    refine ⟨204880929685371134060568887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136587286456914089373712591 204880929685371134060568887)
    ·
      refine ⟨307321394528056701090853331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204880929685371134060568887 307321394528056701090853331)
      ·
        refine ⟨460982091792085051636279997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307321394528056701090853331 460982091792085051636279997)
        ·
          refine ⟨172868284422031894363604999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460982091792085051636279997 172868284422031894363604999)
          ·
            refine ⟨259302426633047841545407499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172868284422031894363604999 259302426633047841545407499)
            ·
              refine ⟨388953639949571762318111249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259302426633047841545407499 388953639949571762318111249)
              ·
                refine ⟨291715229962178821738583437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388953639949571762318111249 291715229962178821738583437)
                ·
                  refine ⟨109393211235817058151968789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291715229962178821738583437 109393211235817058151968789)
                  ·
                    refine ⟨5127806776678924600873537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109393211235817058151968789 5127806776678924600873537)
                    ·
                      refine ⟨3845855082509193450655153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5127806776678924600873537 3845855082509193450655153)
                      ·
                        rfl

theorem cell23_7489776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 6, 2].length) (baseStart_7489776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489776 prefixEnd_7489776 := by exact prefixLift 7489776
  have htrace : WordTrace (prefixWord ++ tailWord_7489776) baseStart_7489776 baseEnd_7489776 := by
    simpa [prefixWord, tailWord_7489776, baseEnd_7489776] using wordTrace_append hprefix tailTrace_7489776
  have hstable : (prefixWord ++ tailWord_7489776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489776).length < 2 ^ (prefixWord ++ tailWord_7489776).sum := by decide
  have hdescent : baseEnd_7489776 < baseStart_7489776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489779 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 5]
def baseStart_7489779 : Nat := 118140960795 + 7489779 * 2 ^ 59
def prefixEnd_7489779 : Nat := 4983230072969 + 3 ^ 40 * 7489779 * 2
def baseEnd_7489779 : Nat := 3845856622951156938917639

theorem tailTrace_7489779 : CollatzResearch.WordTrace tailWord_7489779 prefixEnd_7489779 3845856622951156938917639 := by
  unfold tailWord_7489779
  simp only [CollatzResearch.WordTrace]
  refine ⟨273174682332817310259784391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182116454888544873506522927 273174682332817310259784391)
  ·
    refine ⟨409762023499225965389676587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273174682332817310259784391 409762023499225965389676587)
    ·
      refine ⟨614643035248838948084514881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409762023499225965389676587 614643035248838948084514881)
      ·
        refine ⟨460982276436629211063386161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614643035248838948084514881 460982276436629211063386161)
        ·
          refine ⟨345736707327471908297539621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460982276436629211063386161 345736707327471908297539621)
          ·
            refine ⟨64825632623900982805788679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 345736707327471908297539621 64825632623900982805788679)
            ·
              refine ⟨97238448935851474208683019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64825632623900982805788679 97238448935851474208683019)
              ·
                refine ⟨145857673403777211313024529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97238448935851474208683019 145857673403777211313024529)
                ·
                  refine ⟨109393255052832908484768397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145857673403777211313024529 109393255052832908484768397)
                  ·
                    refine ⟨41022470644812340681788149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109393255052832908484768397 41022470644812340681788149)
                    ·
                      refine ⟨3845856622951156938917639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41022470644812340681788149 3845856622951156938917639)
                      ·
                        rfl

theorem cell23_7489779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_7489779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489779 prefixEnd_7489779 := by exact prefixLift 7489779
  have htrace : WordTrace (prefixWord ++ tailWord_7489779) baseStart_7489779 baseEnd_7489779 := by
    simpa [prefixWord, tailWord_7489779, baseEnd_7489779] using wordTrace_append hprefix tailTrace_7489779
  have hstable : (prefixWord ++ tailWord_7489779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489779).length < 2 ^ (prefixWord ++ tailWord_7489779).sum := by decide
  have hdescent : baseEnd_7489779 < baseStart_7489779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489793 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_7489793 : Nat := 118140960795 + 7489793 * 2 ^ 59
def prefixEnd_7489793 : Nat := 4983230072969 + 3 ^ 40 * 7489793 * 2
def baseEnd_7489793 : Nat := 3845863811680319884142575

theorem tailTrace_7489793 : CollatzResearch.WordTrace tailWord_7489793 prefixEnd_7489793 3845863811680319884142575 := by
  unfold tailWord_7489793
  simp only [CollatzResearch.WordTrace]
  refine ⟨273175192954766590650794033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182116795303177727100529355 273175192954766590650794033)
  ·
    refine ⟨204881394716074942988095525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273175192954766590650794033 204881394716074942988095525)
    ·
      refine ⟨38415261509264051810267911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204881394716074942988095525 38415261509264051810267911)
      ·
        refine ⟨57622892263896077715401867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38415261509264051810267911 57622892263896077715401867)
        ·
          refine ⟨86434338395844116573102801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57622892263896077715401867 86434338395844116573102801)
          ·
            refine ⟨64825753796883087429827101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86434338395844116573102801 64825753796883087429827101)
            ·
              refine ⟨24309657673831157786185163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64825753796883087429827101 24309657673831157786185163)
              ·
                refine ⟨36464486510746736679277745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24309657673831157786185163 36464486510746736679277745)
                ·
                  refine ⟨27348364883060052509458309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36464486510746736679277745 27348364883060052509458309)
                  ·
                    refine ⟨5127818415573759845523433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27348364883060052509458309 5127818415573759845523433)
                    ·
                      refine ⟨3845863811680319884142575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5127818415573759845523433 3845863811680319884142575)
                      ·
                        rfl

theorem cell23_7489793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_7489793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489793 prefixEnd_7489793 := by exact prefixLift 7489793
  have htrace : WordTrace (prefixWord ++ tailWord_7489793) baseStart_7489793 baseEnd_7489793 := by
    simpa [prefixWord, tailWord_7489793, baseEnd_7489793] using wordTrace_append hprefix tailTrace_7489793
  have hstable : (prefixWord ++ tailWord_7489793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489793).length < 2 ^ (prefixWord ++ tailWord_7489793).sum := by decide
  have hdescent : baseEnd_7489793 < baseStart_7489793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489813 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_7489813 : Nat := 118140960795 + 7489813 * 2 ^ 59
def prefixEnd_7489813 : Nat := 4983230072969 + 3 ^ 40 * 7489813 * 2
def baseEnd_7489813 : Nat := 3845874081293409805892483

theorem tailTrace_7489813 : CollatzResearch.WordTrace tailWord_7489813 prefixEnd_7489813 3845874081293409805892483 := by
  unfold tailWord_7489813
  simp only [CollatzResearch.WordTrace]
  refine ⟨273175922414694134066522093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182117281609796089377681395 273175922414694134066522093)
  ·
    refine ⟨102440970905510300274945785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273175922414694134066522093 102440970905510300274945785)
    ·
      refine ⟨76830728179132725206209339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102440970905510300274945785 76830728179132725206209339)
      ·
        refine ⟨115246092268699087809314009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76830728179132725206209339 115246092268699087809314009)
        ·
          refine ⟨86434569201524315856985507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115246092268699087809314009 86434569201524315856985507)
          ·
            refine ⟨129651853802286473785478261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86434569201524315856985507 129651853802286473785478261)
            ·
              refine ⟨12154861293964356917388587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129651853802286473785478261 12154861293964356917388587)
              ·
                refine ⟨18232291940946535376082881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12154861293964356917388587 18232291940946535376082881)
                ·
                  refine ⟨13674218955709901532062161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18232291940946535376082881 13674218955709901532062161)
                  ·
                    refine ⟨10255664216782426149046621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13674218955709901532062161 10255664216782426149046621)
                    ·
                      refine ⟨3845874081293409805892483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10255664216782426149046621 3845874081293409805892483)
                      ·
                        rfl

theorem cell23_7489813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_7489813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489813 prefixEnd_7489813 := by exact prefixLift 7489813
  have htrace : WordTrace (prefixWord ++ tailWord_7489813) baseStart_7489813 baseEnd_7489813 := by
    simpa [prefixWord, tailWord_7489813, baseEnd_7489813] using wordTrace_append hprefix tailTrace_7489813
  have hstable : (prefixWord ++ tailWord_7489813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489813).length < 2 ^ (prefixWord ++ tailWord_7489813).sum := by decide
  have hdescent : baseEnd_7489813 < baseStart_7489813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489837 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_7489837 : Nat := 118140960795 + 7489837 * 2 ^ 59
def prefixEnd_7489837 : Nat := 4983230072969 + 3 ^ 40 * 7489837 * 2
def baseEnd_7489837 : Nat := 1281962134943039237330791

theorem tailTrace_7489837 : CollatzResearch.WordTrace tailWord_7489837 prefixEnd_7489837 1281962134943039237330791 := by
  unfold tailWord_7489837
  simp only [CollatzResearch.WordTrace]
  refine ⟨273176797766607186165395765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182117865177738124110263843 273176797766607186165395765)
  ·
    refine ⟨25610324790619423703005853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273176797766607186165395765 25610324790619423703005853)
    ·
      refine ⟨9603871796482283888627195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25610324790619423703005853 9603871796482283888627195)
      ·
        refine ⟨14405807694723425832940793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9603871796482283888627195 14405807694723425832940793)
        ·
          refine ⟨10804355771042569374705595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14405807694723425832940793 10804355771042569374705595)
          ·
            refine ⟨16206533656563854062058393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10804355771042569374705595 16206533656563854062058393)
            ·
              refine ⟨12154900242422890546543795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16206533656563854062058393 12154900242422890546543795)
              ·
                refine ⟨18232350363634335819815693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12154900242422890546543795 18232350363634335819815693)
                ·
                  refine ⟨6837131386362875932430885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18232350363634335819815693 6837131386362875932430885)
                  ·
                    refine ⟨1281962134943039237330791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6837131386362875932430885 1281962134943039237330791)
                    ·
                      rfl

theorem cell23_7489837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_7489837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489837 prefixEnd_7489837 := by exact prefixLift 7489837
  have htrace : WordTrace (prefixWord ++ tailWord_7489837) baseStart_7489837 baseEnd_7489837 := by
    simpa [prefixWord, tailWord_7489837, baseEnd_7489837] using wordTrace_append hprefix tailTrace_7489837
  have hstable : (prefixWord ++ tailWord_7489837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489837).length < 2 ^ (prefixWord ++ tailWord_7489837).sum := by decide
  have hdescent : baseEnd_7489837 < baseStart_7489837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489863 : List Nat := [1, 1, 4, 1, 2, 2, 4, 2, 1, 5]
def baseStart_7489863 : Nat := 118140960795 + 7489863 * 2 ^ 59
def prefixEnd_7489863 : Nat := 4983230072969 + 3 ^ 40 * 7489863 * 2
def baseEnd_7489863 : Nat := 1281966585108711536755751

theorem tailTrace_7489863 : CollatzResearch.WordTrace tailWord_7489863 prefixEnd_7489863 1281966585108711536755751 := by
  unfold tailWord_7489863
  simp only [CollatzResearch.WordTrace]
  refine ⟨273177746064512992605842243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182118497376341995070561495 273177746064512992605842243)
  ·
    refine ⟨409766619096769488908763365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273177746064512992605842243 409766619096769488908763365)
    ·
      refine ⟨76831241080644279170393131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409766619096769488908763365 76831241080644279170393131)
      ·
        refine ⟨115246861620966418755589697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76831241080644279170393131 115246861620966418755589697)
        ·
          refine ⟨86435146215724814066692273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115246861620966418755589697 86435146215724814066692273)
          ·
            refine ⟨64826359661793610550019205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86435146215724814066692273 64826359661793610550019205)
            ·
              refine ⟨12154942436586301978128601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64826359661793610550019205 12154942436586301978128601)
              ·
                refine ⟨9116206827439726483596451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12154942436586301978128601 9116206827439726483596451)
                ·
                  refine ⟨13674310241159589725394677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9116206827439726483596451 13674310241159589725394677)
                  ·
                    refine ⟨1281966585108711536755751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13674310241159589725394677 1281966585108711536755751)
                    ·
                      rfl

theorem cell23_7489863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_7489863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489863 prefixEnd_7489863 := by exact prefixLift 7489863
  have htrace : WordTrace (prefixWord ++ tailWord_7489863) baseStart_7489863 baseEnd_7489863 := by
    simpa [prefixWord, tailWord_7489863, baseEnd_7489863] using wordTrace_append hprefix tailTrace_7489863
  have hstable : (prefixWord ++ tailWord_7489863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489863).length < 2 ^ (prefixWord ++ tailWord_7489863).sum := by decide
  have hdescent : baseEnd_7489863 < baseStart_7489863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489893 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 4, 4]
def baseStart_7489893 : Nat := 118140960795 + 7489893 * 2 ^ 59
def prefixEnd_7489893 : Nat := 4983230072969 + 3 ^ 40 * 7489893 * 2
def baseEnd_7489893 : Nat := 1281971719915256497630705

theorem tailTrace_7489893 : CollatzResearch.WordTrace tailWord_7489893 prefixEnd_7489893 1281971719915256497630705 := by
  unfold tailWord_7489893
  simp only [CollatzResearch.WordTrace]
  refine ⟨273178840254404307729434333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182119226836269538486289555 273178840254404307729434333)
  ·
    refine ⟨102442065095401615398537875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273178840254404307729434333 102442065095401615398537875)
    ·
      refine ⟨153663097643102423097806813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102442065095401615398537875 153663097643102423097806813)
      ·
        refine ⟨57623661616163408661677555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153663097643102423097806813 57623661616163408661677555)
        ·
          refine ⟨86435492424245112992516333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57623661616163408661677555 86435492424245112992516333)
          ·
            refine ⟨32413309659091917372193625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86435492424245112992516333 32413309659091917372193625)
            ·
              refine ⟨24309982244318938029145219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32413309659091917372193625 24309982244318938029145219)
              ·
                refine ⟨36464973366478407043717829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24309982244318938029145219 36464973366478407043717829)
                ·
                  refine ⟨6837182506214701320697093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36464973366478407043717829 6837182506214701320697093)
                  ·
                    refine ⟨1281971719915256497630705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6837182506214701320697093 1281971719915256497630705)
                    ·
                      rfl

theorem cell23_7489893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_7489893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489893 prefixEnd_7489893 := by exact prefixLift 7489893
  have htrace : WordTrace (prefixWord ++ tailWord_7489893) baseStart_7489893 baseEnd_7489893 := by
    simpa [prefixWord, tailWord_7489893, baseEnd_7489893] using wordTrace_append hprefix tailTrace_7489893
  have hstable : (prefixWord ++ tailWord_7489893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489893).length < 2 ^ (prefixWord ++ tailWord_7489893).sum := by decide
  have hdescent : baseEnd_7489893 < baseStart_7489893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489906 : List Nat := [3, 2, 1, 2, 1, 3, 1, 10]
def baseStart_7489906 : Nat := 118140960795 + 7489906 * 2 ^ 59
def prefixEnd_7489906 : Nat := 4983230072969 + 3 ^ 40 * 7489906 * 2
def baseEnd_7489906 : Nat := 142441549444232516371465

theorem tailTrace_7489906 : CollatzResearch.WordTrace tailWord_7489906 prefixEnd_7489906 142441549444232516371465 := by
  unfold tailWord_7489906
  simp only [CollatzResearch.WordTrace]
  refine ⟨68294828600839302737414393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182119542935571473966438381 68294828600839302737414393)
  ·
    refine ⟨51221121450629477053060795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68294828600839302737414393 51221121450629477053060795)
    ·
      refine ⟨76831682175944215579591193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51221121450629477053060795 76831682175944215579591193)
      ·
        refine ⟨57623761631958161684693395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76831682175944215579591193 57623761631958161684693395)
        ·
          refine ⟨86435642447937242527040093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57623761631958161684693395 86435642447937242527040093)
          ·
            refine ⟨32413365917976465947640035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86435642447937242527040093 32413365917976465947640035)
            ·
              refine ⟨48620048876964698921460053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32413365917976465947640035 48620048876964698921460053)
              ·
                refine ⟨142441549444232516371465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48620048876964698921460053 142441549444232516371465)
                ·
                  rfl

theorem cell23_7489906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 10].length) (baseStart_7489906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489906 prefixEnd_7489906 := by exact prefixLift 7489906
  have htrace : WordTrace (prefixWord ++ tailWord_7489906) baseStart_7489906 baseEnd_7489906 := by
    simpa [prefixWord, tailWord_7489906, baseEnd_7489906] using wordTrace_append hprefix tailTrace_7489906
  have hstable : (prefixWord ++ tailWord_7489906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489906).length < 2 ^ (prefixWord ++ tailWord_7489906).sum := by decide
  have hdescent : baseEnd_7489906 < baseStart_7489906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489985 : List Nat := [1, 2, 7, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7489985 : Nat := 118140960795 + 7489985 * 2 ^ 59
def prefixEnd_7489985 : Nat := 4983230072969 + 3 ^ 40 * 7489985 * 2
def baseEnd_7489985 : Nat := 3845962399965983132941693

theorem tailTrace_7489985 : CollatzResearch.WordTrace tailWord_7489985 prefixEnd_7489985 3845962399965983132941693 := by
  unfold tailWord_7489985
  simp only [CollatzResearch.WordTrace]
  refine ⟨273182195770071007441783409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182121463846714004961188939 273182195770071007441783409)
  ·
    refine ⟨204886646827553255581337557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273182195770071007441783409 204886646827553255581337557)
    ·
      refine ⟨4802030785020779427687599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 204886646827553255581337557 4802030785020779427687599)
      ·
        refine ⟨7203046177531169141531399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4802030785020779427687599 7203046177531169141531399)
        ·
          refine ⟨10804569266296753712297099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7203046177531169141531399 10804569266296753712297099)
          ·
            refine ⟨16206853899445130568445649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10804569266296753712297099 16206853899445130568445649)
            ·
              refine ⟨12155140424583847926334237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16206853899445130568445649 12155140424583847926334237)
              ·
                refine ⟨4558177659218942972375339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12155140424583847926334237 4558177659218942972375339)
                ·
                  refine ⟨6837266488828414458563009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4558177659218942972375339 6837266488828414458563009)
                  ·
                    refine ⟨5127949866621310843922257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6837266488828414458563009 5127949866621310843922257)
                    ·
                      refine ⟨3845962399965983132941693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5127949866621310843922257 3845962399965983132941693)
                      ·
                        rfl

theorem cell23_7489985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7489985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489985 prefixEnd_7489985 := by exact prefixLift 7489985
  have htrace : WordTrace (prefixWord ++ tailWord_7489985) baseStart_7489985 baseEnd_7489985 := by
    simpa [prefixWord, tailWord_7489985, baseEnd_7489985] using wordTrace_append hprefix tailTrace_7489985
  have hstable : (prefixWord ++ tailWord_7489985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489985).length < 2 ^ (prefixWord ++ tailWord_7489985).sum := by decide
  have hdescent : baseEnd_7489985 < baseStart_7489985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490018 : List Nat := [3, 3, 3, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_7490018 : Nat := 118140960795 + 7490018 * 2 ^ 59
def prefixEnd_7490018 : Nat := 4983230072969 + 3 ^ 40 * 7490018 * 2
def baseEnd_7490018 : Nat := 3845979344827581503829041

theorem tailTrace_7490018 : CollatzResearch.WordTrace tailWord_7490018 prefixEnd_7490018 3845979344827581503829041 := by
  unfold tailWord_7490018
  simp only [CollatzResearch.WordTrace]
  refine ⟨68295849844737863519433677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182122266252634302718489805 68295849844737863519433677)
  ·
    refine ⟨25610943691776698819787629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68295849844737863519433677 25610943691776698819787629)
    ·
      refine ⟨9604103884416262057420361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25610943691776698819787629 9604103884416262057420361)
      ·
        refine ⟨7203077913312196543065271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9604103884416262057420361 7203077913312196543065271)
        ·
          refine ⟨10804616869968294814597907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7203077913312196543065271 10804616869968294814597907)
          ·
            refine ⟨16206925304952442221896861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10804616869968294814597907 16206925304952442221896861)
            ·
              refine ⟨6077596989357165833211323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16206925304952442221896861 6077596989357165833211323)
              ·
                refine ⟨9116395484035748749816985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6077596989357165833211323 9116395484035748749816985)
                ·
                  refine ⟨6837296613026811562362739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9116395484035748749816985 6837296613026811562362739)
                  ·
                    refine ⟨10255944919540217343544109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6837296613026811562362739 10255944919540217343544109)
                    ·
                      refine ⟨3845979344827581503829041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10255944919540217343544109 3845979344827581503829041)
                      ·
                        rfl

theorem cell23_7490018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_7490018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490018 prefixEnd_7490018 := by exact prefixLift 7490018
  have htrace : WordTrace (prefixWord ++ tailWord_7490018) baseStart_7490018 baseEnd_7490018 := by
    simpa [prefixWord, tailWord_7490018, baseEnd_7490018] using wordTrace_append hprefix tailTrace_7490018
  have hstable : (prefixWord ++ tailWord_7490018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490018).length < 2 ^ (prefixWord ++ tailWord_7490018).sum := by decide
  have hdescent : baseEnd_7490018 < baseStart_7490018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490060 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 2, 5]
def baseStart_7490060 : Nat := 118140960795 + 7490060 * 2 ^ 59
def prefixEnd_7490060 : Nat := 4983230072969 + 3 ^ 40 * 7490060 * 2
def baseEnd_7490060 : Nat := 1282000303671690113167949

theorem tailTrace_7490060 : CollatzResearch.WordTrace tailWord_7490060 prefixEnd_7490060 1282000303671690113167949 := by
  unfold tailWord_7490060
  simp only [CollatzResearch.WordTrace]
  refine ⟨136592465622399647625381817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182123287496532863500509089 136592465622399647625381817)
  ·
    refine ⟨102444349216799735719036363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136592465622399647625381817 102444349216799735719036363)
    ·
      refine ⟨153666523825199603578554545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102444349216799735719036363 153666523825199603578554545)
      ·
        refine ⟨115249892868899702683915909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153666523825199603578554545 115249892868899702683915909)
        ·
          refine ⟨21609354912918694253234233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115249892868899702683915909 21609354912918694253234233)
          ·
            refine ⟨16207016184689020689925675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21609354912918694253234233 16207016184689020689925675)
            ·
              refine ⟨24310524277033531034888513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16207016184689020689925675 24310524277033531034888513)
              ·
                refine ⟨18232893207775148276166385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24310524277033531034888513 18232893207775148276166385)
                ·
                  refine ⟨13674669905831361207124789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18232893207775148276166385 13674669905831361207124789)
                  ·
                    refine ⟨1282000303671690113167949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13674669905831361207124789 1282000303671690113167949)
                    ·
                      rfl

theorem cell23_7490060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_7490060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490060 prefixEnd_7490060 := by exact prefixLift 7490060
  have htrace : WordTrace (prefixWord ++ tailWord_7490060) baseStart_7490060 baseEnd_7490060 := by
    simpa [prefixWord, tailWord_7490060, baseEnd_7490060] using wordTrace_append hprefix tailTrace_7490060
  have hstable : (prefixWord ++ tailWord_7490060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490060).length < 2 ^ (prefixWord ++ tailWord_7490060).sum := by decide
  have hdescent : baseEnd_7490060 < baseStart_7490060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490063 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 4]
def baseStart_7490063 : Nat := 118140960795 + 7490063 * 2 ^ 59
def prefixEnd_7490063 : Nat := 4983230072969 + 3 ^ 40 * 7490063 * 2
def baseEnd_7490063 : Nat := 3846002451457033827766333

theorem tailTrace_7490063 : CollatzResearch.WordTrace tailWord_7490063 prefixEnd_7490063 3846002451457033827766333 := by
  unfold tailWord_7490063
  simp only [CollatzResearch.WordTrace]
  refine ⟨273185040663788426763122843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182123360442525617842081895 273185040663788426763122843)
  ·
    refine ⟨409777560995682640144684265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273185040663788426763122843 409777560995682640144684265)
    ·
      refine ⟨307333170746761980108513199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409777560995682640144684265 307333170746761980108513199)
      ·
        refine ⟨460999756120142970162769799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307333170746761980108513199 460999756120142970162769799)
        ·
          refine ⟨691499634180214455244154699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460999756120142970162769799 691499634180214455244154699)
          ·
            refine ⟨1037249451270321682866232049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691499634180214455244154699 1037249451270321682866232049)
            ·
              refine ⟨777937088452741262149674037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1037249451270321682866232049 777937088452741262149674037)
              ·
                refine ⟨72931602042444493326531941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 777937088452741262149674037 72931602042444493326531941)
                ·
                  refine ⟨13674675382958342498724739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72931602042444493326531941 13674675382958342498724739)
                  ·
                    refine ⟨20512013074437513748087109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13674675382958342498724739 20512013074437513748087109)
                    ·
                      refine ⟨3846002451457033827766333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20512013074437513748087109 3846002451457033827766333)
                      ·
                        rfl

theorem cell23_7490063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_7490063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490063 prefixEnd_7490063 := by exact prefixLift 7490063
  have htrace : WordTrace (prefixWord ++ tailWord_7490063) baseStart_7490063 baseEnd_7490063 := by
    simpa [prefixWord, tailWord_7490063, baseEnd_7490063] using wordTrace_append hprefix tailTrace_7490063
  have hstable : (prefixWord ++ tailWord_7490063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490063).length < 2 ^ (prefixWord ++ tailWord_7490063).sum := by decide
  have hdescent : baseEnd_7490063 < baseStart_7490063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490147 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 3, 1, 3]
def baseStart_7490147 : Nat := 118140960795 + 7490147 * 2 ^ 59
def prefixEnd_7490147 : Nat := 4983230072969 + 3 ^ 40 * 7490147 * 2
def baseEnd_7490147 : Nat := 3846045583832011499115947

theorem tailTrace_7490147 : CollatzResearch.WordTrace tailWord_7490147 prefixEnd_7490147 3846045583832011499115947 := by
  unfold tailWord_7490147
  simp only [CollatzResearch.WordTrace]
  refine ⟨273188104395484109109180695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182125402930322739406120463 273188104395484109109180695)
  ·
    refine ⟨409782156593226163663771043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273188104395484109109180695 409782156593226163663771043)
    ·
      refine ⟨614673234889839245495656565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409782156593226163663771043 614673234889839245495656565)
      ·
        refine ⟨57625615770922429265217803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 614673234889839245495656565 57625615770922429265217803)
        ·
          refine ⟨86438423656383643897826705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57625615770922429265217803 86438423656383643897826705)
          ·
            refine ⟨64828817742287732923370029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86438423656383643897826705 64828817742287732923370029)
            ·
              refine ⟨24310806653357899846263761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64828817742287732923370029 24310806653357899846263761)
              ·
                refine ⟨18233104990018424884697821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24310806653357899846263761 18233104990018424884697821)
                ·
                  refine ⟨6837414371256909331761683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18233104990018424884697821 6837414371256909331761683)
                  ·
                    refine ⟨10256121556885363997642525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6837414371256909331761683 10256121556885363997642525)
                    ·
                      refine ⟨3846045583832011499115947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10256121556885363997642525 3846045583832011499115947)
                      ·
                        rfl

theorem cell23_7490147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_7490147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490147 prefixEnd_7490147 := by exact prefixLift 7490147
  have htrace : WordTrace (prefixWord ++ tailWord_7490147) baseStart_7490147 baseEnd_7490147 := by
    simpa [prefixWord, tailWord_7490147, baseEnd_7490147] using wordTrace_append hprefix tailTrace_7490147
  have hstable : (prefixWord ++ tailWord_7490147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490147).length < 2 ^ (prefixWord ++ tailWord_7490147).sum := by decide
  have hdescent : baseEnd_7490147 < baseStart_7490147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490163 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 3, 6]
def baseStart_7490163 : Nat := 118140960795 + 7490163 * 2 ^ 59
def prefixEnd_7490163 : Nat := 4983230072969 + 3 ^ 40 * 7490163 * 2
def baseEnd_7490163 : Nat := 1282017933174161145505291

theorem tailTrace_7490163 : CollatzResearch.WordTrace tailWord_7490163 prefixEnd_7490163 1282017933174161145505291 := by
  unfold tailWord_7490163
  simp only [CollatzResearch.WordTrace]
  refine ⟨273188687963426143841763143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182125791975617429227842095 273188687963426143841763143)
  ·
    refine ⟨409783031945139215762644715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273188687963426143841763143 409783031945139215762644715)
    ·
      refine ⟨614674547917708823643967073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409783031945139215762644715 614674547917708823643967073)
      ·
        refine ⟨461005910938281617732975305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614674547917708823643967073 461005910938281617732975305)
        ·
          refine ⟨345754433203711213299731479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461005910938281617732975305 345754433203711213299731479)
          ·
            refine ⟨518631649805566819949597219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345754433203711213299731479 518631649805566819949597219)
            ·
              refine ⟨777947474708350229924395829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518631649805566819949597219 777947474708350229924395829)
              ·
                refine ⟨72932575753907834055412109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 777947474708350229924395829 72932575753907834055412109)
                ·
                  refine ⟨27349715907715437770779541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72932575753907834055412109 27349715907715437770779541)
                  ·
                    refine ⟨1282017933174161145505291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27349715907715437770779541 1282017933174161145505291)
                    ·
                      rfl

theorem cell23_7490163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 6].length) (baseStart_7490163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490163 prefixEnd_7490163 := by exact prefixLift 7490163
  have htrace : WordTrace (prefixWord ++ tailWord_7490163) baseStart_7490163 baseEnd_7490163 := by
    simpa [prefixWord, tailWord_7490163, baseEnd_7490163] using wordTrace_append hprefix tailTrace_7490163
  have hstable : (prefixWord ++ tailWord_7490163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490163).length < 2 ^ (prefixWord ++ tailWord_7490163).sum := by decide
  have hdescent : baseEnd_7490163 < baseStart_7490163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490167 : List Nat := [1, 1, 3, 1, 1, 3, 6, 1, 1, 5]
def baseStart_7490167 : Nat := 118140960795 + 7490167 * 2 ^ 59
def prefixEnd_7490167 : Nat := 4983230072969 + 3 ^ 40 * 7490167 * 2
def baseEnd_7490167 : Nat := 1282018617815033806955285

theorem tailTrace_7490167 : CollatzResearch.WordTrace tailWord_7490167 prefixEnd_7490167 1282018617815033806955285 := by
  unfold tailWord_7490167
  simp only [CollatzResearch.WordTrace]
  refine ⟨273188833855411652524908755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182125889236941101683272503 273188833855411652524908755)
  ·
    refine ⟨409783250783117478787363133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273188833855411652524908755 409783250783117478787363133)
    ·
      refine ⟨153668719043669054545261175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409783250783117478787363133 153668719043669054545261175)
      ·
        refine ⟨230503078565503581817891763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153668719043669054545261175 230503078565503581817891763)
        ·
          refine ⟨345754617848255372726837645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230503078565503581817891763 345754617848255372726837645)
          ·
            refine ⟨129657981693095764772564117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345754617848255372726837645 129657981693095764772564117)
            ·
              refine ⟨6077717891863863973713943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129657981693095764772564117 6077717891863863973713943)
              ·
                refine ⟨9116576837795795960570915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6077717891863863973713943 9116576837795795960570915)
                ·
                  refine ⟨13674865256693693940856373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9116576837795795960570915 13674865256693693940856373)
                  ·
                    refine ⟨1282018617815033806955285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13674865256693693940856373 1282018617815033806955285)
                    ·
                      rfl

theorem cell23_7490167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_7490167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490167 prefixEnd_7490167 := by exact prefixLift 7490167
  have htrace : WordTrace (prefixWord ++ tailWord_7490167) baseStart_7490167 baseEnd_7490167 := by
    simpa [prefixWord, tailWord_7490167, baseEnd_7490167] using wordTrace_append hprefix tailTrace_7490167
  have hstable : (prefixWord ++ tailWord_7490167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490167).length < 2 ^ (prefixWord ++ tailWord_7490167).sum := by decide
  have hdescent : baseEnd_7490167 < baseStart_7490167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490200 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_7490200 : Nat := 118140960795 + 7490200 * 2 ^ 59
def prefixEnd_7490200 : Nat := 4983230072969 + 3 ^ 40 * 7490200 * 2
def baseEnd_7490200 : Nat := 3846072798306699791753203

theorem tailTrace_7490200 : CollatzResearch.WordTrace tailWord_7490200 prefixEnd_7490200 3846072798306699791753203 := by
  unfold tailWord_7490200
  simp only [CollatzResearch.WordTrace]
  refine ⟨136595018732146049580430027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182126691642861399440573369 136595018732146049580430027)
  ·
    refine ⟨204892528098219074370645041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136595018732146049580430027 204892528098219074370645041)
    ·
      refine ⟨153669396073664305777983781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204892528098219074370645041 153669396073664305777983781)
      ·
        refine ⟨28813011763812057333371959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153669396073664305777983781 28813011763812057333371959)
        ·
          refine ⟨43219517645718086000057939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28813011763812057333371959 43219517645718086000057939)
          ·
            refine ⟨64829276468577129000086909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43219517645718086000057939 64829276468577129000086909)
            ·
              refine ⟨24310978675716423375032591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64829276468577129000086909 24310978675716423375032591)
              ·
                refine ⟨36466468013574635062548887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24310978675716423375032591 36466468013574635062548887)
                ·
                  refine ⟨54699702020361952593823331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36466468013574635062548887 54699702020361952593823331)
                  ·
                    refine ⟨82049553030542928890734997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54699702020361952593823331 82049553030542928890734997)
                    ·
                      refine ⟨3846072798306699791753203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82049553030542928890734997 3846072798306699791753203)
                      ·
                        rfl

theorem cell23_7490200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_7490200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490200 prefixEnd_7490200 := by exact prefixLift 7490200
  have htrace : WordTrace (prefixWord ++ tailWord_7490200) baseStart_7490200 baseEnd_7490200 := by
    simpa [prefixWord, tailWord_7490200, baseEnd_7490200] using wordTrace_append hprefix tailTrace_7490200
  have hstable : (prefixWord ++ tailWord_7490200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490200).length < 2 ^ (prefixWord ++ tailWord_7490200).sum := by decide
  have hdescent : baseEnd_7490200 < baseStart_7490200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490204 : List Nat := [2, 2, 3, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_7490204 : Nat := 118140960795 + 7490204 * 2 ^ 59
def prefixEnd_7490204 : Nat := 4983230072969 + 3 ^ 40 * 7490204 * 2
def baseEnd_7490204 : Nat := 3846074852229317776103185

theorem tailTrace_7490204 : CollatzResearch.WordTrace tailWord_7490204 prefixEnd_7490204 3846074852229317776103185 := by
  unfold tailWord_7490204
  simp only [CollatzResearch.WordTrace]
  refine ⟨136595091678138803922002833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182126788904185071896003777 136595091678138803922002833)
  ·
    refine ⟨102446318758604102941502125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136595091678138803922002833 102446318758604102941502125)
    ·
      refine ⟨38417369534476538603063297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102446318758604102941502125 38417369534476538603063297)
      ·
        refine ⟨28813027150857403952297473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38417369534476538603063297 28813027150857403952297473)
        ·
          refine ⟨21609770363143052964223105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28813027150857403952297473 21609770363143052964223105)
          ·
            refine ⟨16207327772357289723167329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21609770363143052964223105 16207327772357289723167329)
            ·
              refine ⟨12155495829267967292375497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16207327772357289723167329 12155495829267967292375497)
              ·
                refine ⟨9116621871950975469281623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12155495829267967292375497 9116621871950975469281623)
                ·
                  refine ⟨13674932807926463203922435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9116621871950975469281623 13674932807926463203922435)
                  ·
                    refine ⟨20512399211889694805883653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13674932807926463203922435 20512399211889694805883653)
                    ·
                      refine ⟨3846074852229317776103185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20512399211889694805883653 3846074852229317776103185)
                      ·
                        rfl

theorem cell23_7490204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_7490204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490204 prefixEnd_7490204 := by exact prefixLift 7490204
  have htrace : WordTrace (prefixWord ++ tailWord_7490204) baseStart_7490204 baseEnd_7490204 := by
    simpa [prefixWord, tailWord_7490204, baseEnd_7490204] using wordTrace_append hprefix tailTrace_7490204
  have hstable : (prefixWord ++ tailWord_7490204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490204).length < 2 ^ (prefixWord ++ tailWord_7490204).sum := by decide
  have hdescent : baseEnd_7490204 < baseStart_7490204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490215 : List Nat := [1, 1, 6, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_7490215 : Nat := 118140960795 + 7490215 * 2 ^ 59
def prefixEnd_7490215 : Nat := 4983230072969 + 3 ^ 40 * 7490215 * 2
def baseEnd_7490215 : Nat := 3846080500516517233065635

theorem tailTrace_7490215 : CollatzResearch.WordTrace tailWord_7490215 prefixEnd_7490215 3846080500516517233065635 := by
  unfold tailWord_7490215
  simp only [CollatzResearch.WordTrace]
  refine ⟨273190584559237756722656099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182127056372825171148437399 273190584559237756722656099)
  ·
    refine ⟨409785876838856635083984149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273190584559237756722656099 409785876838856635083984149)
    ·
      refine ⟨19208712976821404769561757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 409785876838856635083984149 19208712976821404769561757)
      ·
        refine ⟨7203267366308026788585659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19208712976821404769561757 7203267366308026788585659)
        ·
          refine ⟨10804901049462040182878489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7203267366308026788585659 10804901049462040182878489)
          ·
            refine ⟨8103675787096530137158867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10804901049462040182878489 8103675787096530137158867)
            ·
              refine ⟨12155513680644795205738301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8103675787096530137158867 12155513680644795205738301)
              ·
                refine ⟨4558317630241798202151863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12155513680644795205738301 4558317630241798202151863)
                ·
                  refine ⟨6837476445362697303227795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4558317630241798202151863 6837476445362697303227795)
                  ·
                    refine ⟨10256214668044045954841693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6837476445362697303227795 10256214668044045954841693)
                    ·
                      refine ⟨3846080500516517233065635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10256214668044045954841693 3846080500516517233065635)
                      ·
                        rfl

theorem cell23_7490215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_7490215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490215 prefixEnd_7490215 := by exact prefixLift 7490215
  have htrace : WordTrace (prefixWord ++ tailWord_7490215) baseStart_7490215 baseEnd_7490215 := by
    simpa [prefixWord, tailWord_7490215, baseEnd_7490215] using wordTrace_append hprefix tailTrace_7490215
  have hstable : (prefixWord ++ tailWord_7490215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490215).length < 2 ^ (prefixWord ++ tailWord_7490215).sum := by decide
  have hdescent : baseEnd_7490215 < baseStart_7490215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490258 : List Nat := [3, 2, 2, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_7490258 : Nat := 118140960795 + 7490258 * 2 ^ 59
def prefixEnd_7490258 : Nat := 4983230072969 + 3 ^ 40 * 7490258 * 2
def baseEnd_7490258 : Nat := 3846102580184660564827937

theorem tailTrace_7490258 : CollatzResearch.WordTrace tailWord_7490258 prefixEnd_7490258 3846102580184660564827937 := by
  unfold tailWord_7490258
  simp only [CollatzResearch.WordTrace]
  refine ⟨68298038224520493766617857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182128101932054650044314285 68298038224520493766617857)
  ·
    refine ⟨51223528668390370324963393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68298038224520493766617857 51223528668390370324963393)
    ·
      refine ⟨38417646501292777743722545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51223528668390370324963393 38417646501292777743722545)
      ·
        refine ⟨28813234875969583307791909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38417646501292777743722545 28813234875969583307791909)
        ·
          refine ⟨5402481539244296870210983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28813234875969583307791909 5402481539244296870210983)
          ·
            refine ⟨8103722308866445305316475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5402481539244296870210983 8103722308866445305316475)
            ·
              refine ⟨12155583463299667957974713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8103722308866445305316475 12155583463299667957974713)
              ·
                refine ⟨9116687597474750968481035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12155583463299667957974713 9116687597474750968481035)
                ·
                  refine ⟨13675031396212126452721553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9116687597474750968481035 13675031396212126452721553)
                  ·
                    refine ⟨10256273547159094839541165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13675031396212126452721553 10256273547159094839541165)
                    ·
                      refine ⟨3846102580184660564827937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10256273547159094839541165 3846102580184660564827937)
                      ·
                        rfl

theorem cell23_7490258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_7490258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490258 prefixEnd_7490258 := by exact prefixLift 7490258
  have htrace : WordTrace (prefixWord ++ tailWord_7490258) baseStart_7490258 baseEnd_7490258 := by
    simpa [prefixWord, tailWord_7490258, baseEnd_7490258] using wordTrace_append hprefix tailTrace_7490258
  have hstable : (prefixWord ++ tailWord_7490258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490258).length < 2 ^ (prefixWord ++ tailWord_7490258).sum := by decide
  have hdescent : baseEnd_7490258 < baseStart_7490258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490264 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 3, 3, 2]
def baseStart_7490264 : Nat := 118140960795 + 7490264 * 2 ^ 59
def prefixEnd_7490264 : Nat := 4983230072969 + 3 ^ 40 * 7490264 * 2
def baseEnd_7490264 : Nat := 3846105661068587541352909

theorem tailTrace_7490264 : CollatzResearch.WordTrace tailWord_7490264 prefixEnd_7490264 3846105661068587541352909 := by
  unfold tailWord_7490264
  simp only [CollatzResearch.WordTrace]
  refine ⟨136596185868030119045594923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182128247824040158727459897 136596185868030119045594923)
  ·
    refine ⟨204894278802045178568392385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136596185868030119045594923 204894278802045178568392385)
    ·
      refine ⟨153670709101533883926294289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204894278802045178568392385 153670709101533883926294289)
      ·
        refine ⟨115253031826150412944720717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153670709101533883926294289 115253031826150412944720717)
        ·
          refine ⟨43219886934806404854270269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115253031826150412944720717 43219886934806404854270269)
          ·
            refine ⟨16207457600552401820351351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43219886934806404854270269 16207457600552401820351351)
            ·
              refine ⟨24311186400828602730527027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16207457600552401820351351 24311186400828602730527027)
              ·
                refine ⟨36466779601242904095790541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24311186400828602730527027 36466779601242904095790541)
                ·
                  refine ⟨13675042350466089035921453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36466779601242904095790541 13675042350466089035921453)
                  ·
                    refine ⟨5128140881424783388470545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13675042350466089035921453 5128140881424783388470545)
                    ·
                      refine ⟨3846105661068587541352909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5128140881424783388470545 3846105661068587541352909)
                      ·
                        rfl

theorem cell23_7490264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_7490264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490264 prefixEnd_7490264 := by exact prefixLift 7490264
  have htrace : WordTrace (prefixWord ++ tailWord_7490264) baseStart_7490264 baseEnd_7490264 := by
    simpa [prefixWord, tailWord_7490264, baseEnd_7490264] using wordTrace_append hprefix tailTrace_7490264
  have hstable : (prefixWord ++ tailWord_7490264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490264).length < 2 ^ (prefixWord ++ tailWord_7490264).sum := by decide
  have hdescent : baseEnd_7490264 < baseStart_7490264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490294 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_7490294 : Nat := 118140960795 + 7490294 * 2 ^ 59
def prefixEnd_7490294 : Nat := 4983230072969 + 3 ^ 40 * 7490294 * 2
def baseEnd_7490294 : Nat := 3846121065488222423977771

theorem tailTrace_7490294 : CollatzResearch.WordTrace tailWord_7490294 prefixEnd_7490294 3846121065488222423977771 := by
  unfold tailWord_7490294
  simp only [CollatzResearch.WordTrace]
  refine ⟨17074591620371972075923871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182128977283967702143187957 17074591620371972075923871)
  ·
    refine ⟨25611887430557958113885807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17074591620371972075923871 25611887430557958113885807)
    ·
      refine ⟨38417831145836937170828711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25611887430557958113885807 38417831145836937170828711)
      ·
        refine ⟨57626746718755405756243067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38417831145836937170828711 57626746718755405756243067)
        ·
          refine ⟨86440120078133108634364601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57626746718755405756243067 86440120078133108634364601)
          ·
            refine ⟨64830090058599831475773451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86440120078133108634364601 64830090058599831475773451)
            ·
              refine ⟨97245135087899747213660177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64830090058599831475773451 97245135087899747213660177)
              ·
                refine ⟨72933851315924810410245133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97245135087899747213660177 72933851315924810410245133)
                ·
                  refine ⟨27350194243471803903841925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72933851315924810410245133 27350194243471803903841925)
                  ·
                    refine ⟨5128161420650963231970361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27350194243471803903841925 5128161420650963231970361)
                    ·
                      refine ⟨3846121065488222423977771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5128161420650963231970361 3846121065488222423977771)
                      ·
                        rfl

theorem cell23_7490294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_7490294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490294 prefixEnd_7490294 := by exact prefixLift 7490294
  have htrace : WordTrace (prefixWord ++ tailWord_7490294) baseStart_7490294 baseEnd_7490294 := by
    simpa [prefixWord, tailWord_7490294, baseEnd_7490294] using wordTrace_append hprefix tailTrace_7490294
  have hstable : (prefixWord ++ tailWord_7490294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490294).length < 2 ^ (prefixWord ++ tailWord_7490294).sum := by decide
  have hdescent : baseEnd_7490294 < baseStart_7490294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490311 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 1, 4, 2]
def baseStart_7490311 : Nat := 118140960795 + 7490311 * 2 ^ 59
def prefixEnd_7490311 : Nat := 4983230072969 + 3 ^ 40 * 7490311 * 2
def baseEnd_7490311 : Nat := 3846129794659348857465193

theorem tailTrace_7490311 : CollatzResearch.WordTrace tailWord_7490311 prefixEnd_7490311 3846129794659348857465193 := by
  unfold tailWord_7490311
  simp only [CollatzResearch.WordTrace]
  refine ⟨273194085966889965118150787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182129390644593310078767191 273194085966889965118150787)
  ·
    refine ⟨409791128950334947677226181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273194085966889965118150787 409791128950334947677226181)
    ·
      refine ⟨76835836678187802689479909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409791128950334947677226181 76835836678187802689479909)
      ·
        refine ⟨14406719377160213004277483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76835836678187802689479909 14406719377160213004277483)
        ·
          refine ⟨21610079065740319506416225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14406719377160213004277483 21610079065740319506416225)
          ·
            refine ⟨16207559299305239629812169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21610079065740319506416225 16207559299305239629812169)
            ·
              refine ⟨12155669474478929722359127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16207559299305239629812169 12155669474478929722359127)
              ·
                refine ⟨18233504211718394583538691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12155669474478929722359127 18233504211718394583538691)
                ·
                  refine ⟨27350256317577591875308037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18233504211718394583538691 27350256317577591875308037)
                  ·
                    refine ⟨5128173059545798476620257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27350256317577591875308037 5128173059545798476620257)
                    ·
                      refine ⟨3846129794659348857465193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5128173059545798476620257 3846129794659348857465193)
                      ·
                        rfl

theorem cell23_7490311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_7490311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490311 prefixEnd_7490311 := by exact prefixLift 7490311
  have htrace : WordTrace (prefixWord ++ tailWord_7490311) baseStart_7490311 baseEnd_7490311 := by
    simpa [prefixWord, tailWord_7490311, baseEnd_7490311] using wordTrace_append hprefix tailTrace_7490311
  have hstable : (prefixWord ++ tailWord_7490311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490311).length < 2 ^ (prefixWord ++ tailWord_7490311).sum := by decide
  have hdescent : baseEnd_7490311 < baseStart_7490311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490367 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 4]
def baseStart_7490367 : Nat := 118140960795 + 7490367 * 2 ^ 59
def prefixEnd_7490367 : Nat := 4983230072969 + 3 ^ 40 * 7490367 * 2
def baseEnd_7490367 : Nat := 3846158549576000638364935

theorem tailTrace_7490367 : CollatzResearch.WordTrace tailWord_7490367 prefixEnd_7490367 3846158549576000638364935 := by
  unfold tailWord_7490367
  simp only [CollatzResearch.WordTrace]
  refine ⟨273196128454687086682189355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182130752303124724454792903 273196128454687086682189355)
  ·
    refine ⟨409794192682030630023284033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273196128454687086682189355 409794192682030630023284033)
    ·
      refine ⟨307345644511522972517463025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409794192682030630023284033 307345644511522972517463025)
      ·
        refine ⟨230509233383642229388097269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307345644511522972517463025 230509233383642229388097269)
        ·
          refine ⟨21610240629716459005134119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230509233383642229388097269 21610240629716459005134119)
          ·
            refine ⟨32415360944574688507701179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21610240629716459005134119 32415360944574688507701179)
            ·
              refine ⟨48623041416862032761551769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32415360944574688507701179 48623041416862032761551769)
              ·
                refine ⟨36467281062646524571163827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48623041416862032761551769 36467281062646524571163827)
                ·
                  refine ⟨54700921593969786856745741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36467281062646524571163827 54700921593969786856745741)
                  ·
                    refine ⟨20512845597738670071279653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54700921593969786856745741 20512845597738670071279653)
                    ·
                      refine ⟨3846158549576000638364935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20512845597738670071279653 3846158549576000638364935)
                      ·
                        rfl

theorem cell23_7490367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_7490367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490367 prefixEnd_7490367 := by exact prefixLift 7490367
  have htrace : WordTrace (prefixWord ++ tailWord_7490367) baseStart_7490367 baseEnd_7490367 := by
    simpa [prefixWord, tailWord_7490367, baseEnd_7490367] using wordTrace_append hprefix tailTrace_7490367
  have hstable : (prefixWord ++ tailWord_7490367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490367).length < 2 ^ (prefixWord ++ tailWord_7490367).sum := by decide
  have hdescent : baseEnd_7490367 < baseStart_7490367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490387 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 3]
def baseStart_7490387 : Nat := 118140960795 + 7490387 * 2 ^ 59
def prefixEnd_7490387 : Nat := 4983230072969 + 3 ^ 40 * 7490387 * 2
def baseEnd_7490387 : Nat := 3846168819189090560114843

theorem tailTrace_7490387 : CollatzResearch.WordTrace tailWord_7490387 prefixEnd_7490387 3846168819189090560114843 := by
  unfold tailWord_7490387
  simp only [CollatzResearch.WordTrace]
  refine ⟨273196857914614630097917415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182131238609743086731944943 273196857914614630097917415)
  ·
    refine ⟨409795286871921945146876123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273196857914614630097917415 409795286871921945146876123)
    ·
      refine ⟨614692930307882917720314185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409795286871921945146876123 614692930307882917720314185)
      ·
        refine ⟨461019697730912188290235639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614692930307882917720314185 461019697730912188290235639)
        ·
          refine ⟨691529546596368282435353459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461019697730912188290235639 691529546596368282435353459)
          ·
            refine ⟨1037294319894552423653030189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691529546596368282435353459 1037294319894552423653030189)
            ·
              refine ⟨388985369960457158869886321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1037294319894552423653030189 388985369960457158869886321)
              ·
                refine ⟨291739027470342869152414741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388985369960457158869886321 291739027470342869152414741)
                ·
                  refine ⟨13675266912672321991519441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 291739027470342869152414741 13675266912672321991519441)
                  ·
                    refine ⟨10256450184504241493639581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13675266912672321991519441 10256450184504241493639581)
                    ·
                      refine ⟨3846168819189090560114843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10256450184504241493639581 3846168819189090560114843)
                      ·
                        rfl

theorem cell23_7490387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 3].length) (baseStart_7490387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490387 prefixEnd_7490387 := by exact prefixLift 7490387
  have htrace : WordTrace (prefixWord ++ tailWord_7490387) baseStart_7490387 baseEnd_7490387 := by
    simpa [prefixWord, tailWord_7490387, baseEnd_7490387] using wordTrace_append hprefix tailTrace_7490387
  have hstable : (prefixWord ++ tailWord_7490387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490387).length < 2 ^ (prefixWord ++ tailWord_7490387).sum := by decide
  have hdescent : baseEnd_7490387 < baseStart_7490387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490404 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_7490404 : Nat := 118140960795 + 7490404 * 2 ^ 59
def prefixEnd_7490404 : Nat := 4983230072969 + 3 ^ 40 * 7490404 * 2
def baseEnd_7490404 : Nat := 3846177548360216993602265

theorem tailTrace_7490404 : CollatzResearch.WordTrace tailWord_7490404 prefixEnd_7490404 3846177548360216993602265 := by
  unfold tailWord_7490404
  simp only [CollatzResearch.WordTrace]
  refine ⟨136598738977776521000643133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182131651970368694667524177 136598738977776521000643133)
  ·
    refine ⟨51224527116666195375241175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136598738977776521000643133 51224527116666195375241175)
    ·
      refine ⟨76836790674999293062861763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51224527116666195375241175 76836790674999293062861763)
      ·
        refine ⟨115255186012498939594292645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76836790674999293062861763 115255186012498939594292645)
        ·
          refine ⟨21610347377343551173929871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115255186012498939594292645 21610347377343551173929871)
          ·
            refine ⟨32415521066015326760894807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21610347377343551173929871 32415521066015326760894807)
            ·
              refine ⟨48623281599022990141342211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32415521066015326760894807 48623281599022990141342211)
              ·
                refine ⟨72934922398534485212013317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48623281599022990141342211 72934922398534485212013317)
                ·
                  refine ⟨13675297949725215977252497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72934922398534485212013317 13675297949725215977252497)
                  ·
                    refine ⟨10256473462293911982939373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13675297949725215977252497 10256473462293911982939373)
                    ·
                      refine ⟨3846177548360216993602265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10256473462293911982939373 3846177548360216993602265)
                      ·
                        rfl

theorem cell23_7490404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_7490404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490404 prefixEnd_7490404 := by exact prefixLift 7490404
  have htrace : WordTrace (prefixWord ++ tailWord_7490404) baseStart_7490404 baseEnd_7490404 := by
    simpa [prefixWord, tailWord_7490404, baseEnd_7490404] using wordTrace_append hprefix tailTrace_7490404
  have hstable : (prefixWord ++ tailWord_7490404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490404).length < 2 ^ (prefixWord ++ tailWord_7490404).sum := by decide
  have hdescent : baseEnd_7490404 < baseStart_7490404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490407 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 8]
def baseStart_7490407 : Nat := 118140960795 + 7490407 * 2 ^ 59
def prefixEnd_7490407 : Nat := 4983230072969 + 3 ^ 40 * 7490407 * 2
def baseEnd_7490407 : Nat := 427353232089131164651639

theorem tailTrace_7490407 : CollatzResearch.WordTrace tailWord_7490407 prefixEnd_7490407 427353232089131164651639 := by
  unfold tailWord_7490407
  simp only [CollatzResearch.WordTrace]
  refine ⟨273197587374542173513645475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182131724916361449009096983 273197587374542173513645475)
  ·
    refine ⟨409796381061813260270468213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273197587374542173513645475 409796381061813260270468213)
    ·
      refine ⟨38418410724544993150356395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 409796381061813260270468213 38418410724544993150356395)
      ·
        refine ⟨57627616086817489725534593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38418410724544993150356395 57627616086817489725534593)
        ·
          refine ⟨43220712065113117294150945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57627616086817489725534593 43220712065113117294150945)
          ·
            refine ⟨32415534048834837970613209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43220712065113117294150945 32415534048834837970613209)
            ·
              refine ⟨24311650536626128477959907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32415534048834837970613209 24311650536626128477959907)
              ·
                refine ⟨36467475804939192716939861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24311650536626128477959907 36467475804939192716939861)
                ·
                  refine ⟨427353232089131164651639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36467475804939192716939861 427353232089131164651639)
                  ·
                    rfl

theorem cell23_7490407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 8].length) (baseStart_7490407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490407 prefixEnd_7490407 := by exact prefixLift 7490407
  have htrace : WordTrace (prefixWord ++ tailWord_7490407) baseStart_7490407 baseEnd_7490407 := by
    simpa [prefixWord, tailWord_7490407, baseEnd_7490407] using wordTrace_append hprefix tailTrace_7490407
  have hstable : (prefixWord ++ tailWord_7490407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490407).length < 2 ^ (prefixWord ++ tailWord_7490407).sum := by decide
  have hdescent : baseEnd_7490407 < baseStart_7490407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490444 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 1, 5, 2]
def baseStart_7490444 : Nat := 118140960795 + 7490444 * 2 ^ 59
def prefixEnd_7490444 : Nat := 4983230072969 + 3 ^ 40 * 7490444 * 2
def baseEnd_7490444 : Nat := 3846198087586396837102081

theorem tailTrace_7490444 : CollatzResearch.WordTrace tailWord_7490444 prefixEnd_7490444 3846198087586396837102081 := by
  unfold tailWord_7490444
  simp only [CollatzResearch.WordTrace]
  refine ⟨136599468437704064416371193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182132624583605419221828257 136599468437704064416371193)
  ·
    refine ⟨102449601328278048312278395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136599468437704064416371193 102449601328278048312278395)
    ·
      refine ⟨153674401992417072468417593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102449601328278048312278395 153674401992417072468417593)
      ·
        refine ⟨115255801494312804351313195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153674401992417072468417593 115255801494312804351313195)
        ·
          refine ⟨172883702241469206526969793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115255801494312804351313195 172883702241469206526969793)
          ·
            refine ⟨129662776681101904895227345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172883702241469206526969793 129662776681101904895227345)
            ·
              refine ⟨97247082510826428671420509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129662776681101904895227345 97247082510826428671420509)
              ·
                refine ⟨36467655941559910751782691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97247082510826428671420509 36467655941559910751782691)
                ·
                  refine ⟨54701483912339866127674037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36467655941559910751782691 54701483912339866127674037)
                  ·
                    refine ⟨5128264116781862449469441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54701483912339866127674037 5128264116781862449469441)
                    ·
                      refine ⟨3846198087586396837102081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5128264116781862449469441 3846198087586396837102081)
                      ·
                        rfl

theorem cell23_7490444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_7490444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490444 prefixEnd_7490444 := by exact prefixLift 7490444
  have htrace : WordTrace (prefixWord ++ tailWord_7490444) baseStart_7490444 baseEnd_7490444 := by
    simpa [prefixWord, tailWord_7490444, baseEnd_7490444] using wordTrace_append hprefix tailTrace_7490444
  have hstable : (prefixWord ++ tailWord_7490444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490444).length < 2 ^ (prefixWord ++ tailWord_7490444).sum := by decide
  have hdescent : baseEnd_7490444 < baseStart_7490444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490461 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_7490461 : Nat := 118140960795 + 7490461 * 2 ^ 59
def prefixEnd_7490461 : Nat := 4983230072969 + 3 ^ 40 * 7490461 * 2
def baseEnd_7490461 : Nat := 3846206816757523270589503

theorem tailTrace_7490461 : CollatzResearch.WordTrace tailWord_7490461 prefixEnd_7490461 3846206816757523270589503 := by
  unfold tailWord_7490461
  simp only [CollatzResearch.WordTrace]
  refine ⟨273199556916346540736111237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182133037944231027157407491 273199556916346540736111237)
  ·
    refine ⟨51224916921814976388020857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273199556916346540736111237 51224916921814976388020857)
    ·
      refine ⟨38418687691361232291015643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51224916921814976388020857 38418687691361232291015643)
      ·
        refine ⟨57628031537041848436523465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38418687691361232291015643 57628031537041848436523465)
        ·
          refine ⟨43221023652781386327392599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57628031537041848436523465 43221023652781386327392599)
          ·
            refine ⟨64831535479172079491088899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43221023652781386327392599 64831535479172079491088899)
            ·
              refine ⟨97247303218758119236633349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64831535479172079491088899 97247303218758119236633349)
              ·
                refine ⟨18233869353517147356868753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97247303218758119236633349 18233869353517147356868753)
                ·
                  refine ⟨13675402015137860517651565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18233869353517147356868753 13675402015137860517651565)
                  ·
                    refine ⟨5128275755676697694119337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13675402015137860517651565 5128275755676697694119337)
                    ·
                      refine ⟨3846206816757523270589503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5128275755676697694119337 3846206816757523270589503)
                      ·
                        rfl

theorem cell23_7490461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_7490461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490461 prefixEnd_7490461 := by exact prefixLift 7490461
  have htrace : WordTrace (prefixWord ++ tailWord_7490461) baseStart_7490461 baseEnd_7490461 := by
    simpa [prefixWord, tailWord_7490461, baseEnd_7490461] using wordTrace_append hprefix tailTrace_7490461
  have hstable : (prefixWord ++ tailWord_7490461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490461).length < 2 ^ (prefixWord ++ tailWord_7490461).sum := by decide
  have hdescent : baseEnd_7490461 < baseStart_7490461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490468 : List Nat := [2, 3, 1, 2, 1, 2, 3, 4, 1, 1, 3]
def baseStart_7490468 : Nat := 118140960795 + 7490468 * 2 ^ 59
def prefixEnd_7490468 : Nat := 4983230072969 + 3 ^ 40 * 7490468 * 2
def baseEnd_7490468 : Nat := 3846210411122104743201971

theorem tailTrace_7490468 : CollatzResearch.WordTrace tailWord_7490468 prefixEnd_7490468 3846210411122104743201971 := by
  unfold tailWord_7490468
  simp only [CollatzResearch.WordTrace]
  refine ⟨136599906113660590465808029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182133208151547453954410705 136599906113660590465808029)
  ·
    refine ⟨51224964792622721424678011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136599906113660590465808029 51224964792622721424678011)
    ·
      refine ⟨76837447188934082137017017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51224964792622721424678011 76837447188934082137017017)
      ·
        refine ⟨57628085391700561602762763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76837447188934082137017017 57628085391700561602762763)
        ·
          refine ⟨86442128087550842404144145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57628085391700561602762763 86442128087550842404144145)
          ·
            refine ⟨64831596065663131803108109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86442128087550842404144145 64831596065663131803108109)
            ·
              refine ⟨24311848524623674426165541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64831596065663131803108109 24311848524623674426165541)
              ·
                refine ⟨4558471598366938954906039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24311848524623674426165541 4558471598366938954906039)
                ·
                  refine ⟨6837707397550408432359059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4558471598366938954906039 6837707397550408432359059)
                  ·
                    refine ⟨10256561096325612648538589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6837707397550408432359059 10256561096325612648538589)
                    ·
                      refine ⟨3846210411122104743201971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10256561096325612648538589 3846210411122104743201971)
                      ·
                        rfl

theorem cell23_7490468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_7490468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490468 prefixEnd_7490468 := by exact prefixLift 7490468
  have htrace : WordTrace (prefixWord ++ tailWord_7490468) baseStart_7490468 baseEnd_7490468 := by
    simpa [prefixWord, tailWord_7490468, baseEnd_7490468] using wordTrace_append hprefix tailTrace_7490468
  have hstable : (prefixWord ++ tailWord_7490468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490468).length < 2 ^ (prefixWord ++ tailWord_7490468).sum := by decide
  have hdescent : baseEnd_7490468 < baseStart_7490468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490487 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_7490487 : Nat := 118140960795 + 7490487 * 2 ^ 59
def prefixEnd_7490487 : Nat := 4983230072969 + 3 ^ 40 * 7490487 * 2
def baseEnd_7490487 : Nat := 3846220167254540168864383

theorem tailTrace_7490487 : CollatzResearch.WordTrace tailWord_7490487 prefixEnd_7490487 3846220167254540168864383 := by
  unfold tailWord_7490487
  simp only [CollatzResearch.WordTrace]
  refine ⟨273200505214252347176557715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182133670142834898117705143 273200505214252347176557715)
  ·
    refine ⟨409800757821378520764836573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273200505214252347176557715 409800757821378520764836573)
    ·
      refine ⟨153675284183016945286813715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409800757821378520764836573 153675284183016945286813715)
      ·
        refine ⟨230512926274525417930220573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153675284183016945286813715 230512926274525417930220573)
        ·
          refine ⟨86442347352947031723832715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230512926274525417930220573 86442347352947031723832715)
          ·
            refine ⟨129663521029420547585749073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86442347352947031723832715 129663521029420547585749073)
            ·
              refine ⟨97247640772065410689311805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129663521029420547585749073 97247640772065410689311805)
              ·
                refine ⟨36467865289524529008491927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97247640772065410689311805 36467865289524529008491927)
                ·
                  refine ⟨54701797934286793512737891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36467865289524529008491927 54701797934286793512737891)
                  ·
                    refine ⟨82052696901430190269106837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54701797934286793512737891 82052696901430190269106837)
                    ·
                      refine ⟨3846220167254540168864383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82052696901430190269106837 3846220167254540168864383)
                      ·
                        rfl

theorem cell23_7490487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_7490487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490487 prefixEnd_7490487 := by exact prefixLift 7490487
  have htrace : WordTrace (prefixWord ++ tailWord_7490487) baseStart_7490487 baseEnd_7490487 := by
    simpa [prefixWord, tailWord_7490487, baseEnd_7490487] using wordTrace_append hprefix tailTrace_7490487
  have hstable : (prefixWord ++ tailWord_7490487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490487).length < 2 ^ (prefixWord ++ tailWord_7490487).sum := by decide
  have hdescent : baseEnd_7490487 < baseStart_7490487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490511 : List Nat := [1, 1, 2, 1, 1, 7, 1, 3, 1, 2, 3]
def baseStart_7490511 : Nat := 118140960795 + 7490511 * 2 ^ 59
def prefixEnd_7490511 : Nat := 4983230072969 + 3 ^ 40 * 7490511 * 2
def baseEnd_7490511 : Nat := 3846232490790248074964273

theorem tailTrace_7490511 : CollatzResearch.WordTrace tailWord_7490511 prefixEnd_7490511 3846232490790248074964273 := by
  unfold tailWord_7490511
  simp only [CollatzResearch.WordTrace]
  refine ⟨273201380566165399275431387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182134253710776932850287591 273201380566165399275431387)
  ·
    refine ⟨409802070849248098913147081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273201380566165399275431387 409802070849248098913147081)
    ·
      refine ⟨307351553136936074184860311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409802070849248098913147081 307351553136936074184860311)
      ·
        refine ⟨461027329705404111277290467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307351553136936074184860311 461027329705404111277290467)
        ·
          refine ⟨691540994558106166915935701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461027329705404111277290467 691540994558106166915935701)
          ·
            refine ⟨16207992059955613287092243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 691540994558106166915935701 16207992059955613287092243)
            ·
              refine ⟨24311988089933419930638365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16207992059955613287092243 24311988089933419930638365)
              ·
                refine ⟨9116995533725032473989387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24311988089933419930638365 9116995533725032473989387)
                ·
                  refine ⟨13675493300587548710984081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9116995533725032473989387 13675493300587548710984081)
                  ·
                    refine ⟨10256619975440661533238061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13675493300587548710984081 10256619975440661533238061)
                    ·
                      refine ⟨3846232490790248074964273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10256619975440661533238061 3846232490790248074964273)
                      ·
                        rfl

theorem cell23_7490511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 2, 3].length) (baseStart_7490511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490511 prefixEnd_7490511 := by exact prefixLift 7490511
  have htrace : WordTrace (prefixWord ++ tailWord_7490511) baseStart_7490511 baseEnd_7490511 := by
    simpa [prefixWord, tailWord_7490511, baseEnd_7490511] using wordTrace_append hprefix tailTrace_7490511
  have hstable : (prefixWord ++ tailWord_7490511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490511).length < 2 ^ (prefixWord ++ tailWord_7490511).sum := by decide
  have hdescent : baseEnd_7490511 < baseStart_7490511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490514 : List Nat := [3, 2, 2, 3, 1, 2, 10]
def baseStart_7490514 : Nat := 118140960795 + 7490514 * 2 ^ 59
def prefixEnd_7490514 : Nat := 4983230072969 + 3 ^ 40 * 7490514 * 2
def baseEnd_7490514 : Nat := 47484370755953229175639

theorem tailTrace_7490514 : CollatzResearch.WordTrace tailWord_7490514 prefixEnd_7490514 47484370755953229175639 := by
  unfold tailWord_7490514
  simp only [CollatzResearch.WordTrace]
  refine ⟨68300372496288632696947649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182134326656769687191860397 68300372496288632696947649)
  ·
    refine ⟨51225279372216474522710737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68300372496288632696947649 51225279372216474522710737)
    ·
      refine ⟨38418959529162355892033053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51225279372216474522710737 38418959529162355892033053)
      ·
        refine ⟨14407109823435883459512395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38418959529162355892033053 14407109823435883459512395)
        ·
          refine ⟨21610664735153825189268593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14407109823435883459512395 21610664735153825189268593)
          ·
            refine ⟨16207998551365368891951445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21610664735153825189268593 16207998551365368891951445)
            ·
              refine ⟨47484370755953229175639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16207998551365368891951445 47484370755953229175639)
              ·
                rfl

theorem cell23_7490514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 10].length) (baseStart_7490514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490514 prefixEnd_7490514 := by exact prefixLift 7490514
  have htrace : WordTrace (prefixWord ++ tailWord_7490514) baseStart_7490514 baseEnd_7490514 := by
    simpa [prefixWord, tailWord_7490514, baseEnd_7490514] using wordTrace_append hprefix tailTrace_7490514
  have hstable : (prefixWord ++ tailWord_7490514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490514).length < 2 ^ (prefixWord ++ tailWord_7490514).sum := by decide
  have hdescent : baseEnd_7490514 < baseStart_7490514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490518 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_7490518 : Nat := 118140960795 + 7490518 * 2 ^ 59
def prefixEnd_7490518 : Nat := 4983230072969 + 3 ^ 40 * 7490518 * 2
def baseEnd_7490518 : Nat := 1282078695051609849192247

theorem tailTrace_7490518 : CollatzResearch.WordTrace tailWord_7490518 prefixEnd_7490518 1282078695051609849192247 := by
  unfold tailWord_7490518
  simp only [CollatzResearch.WordTrace]
  refine ⟨17075102242321252466933513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182134423918093359647290805 17075102242321252466933513)
  ·
    refine ⟨12806326681740939350200135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17075102242321252466933513 12806326681740939350200135)
    ·
      refine ⟨19209490022611409025300203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12806326681740939350200135 19209490022611409025300203)
      ·
        refine ⟨28814235033917113537950305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19209490022611409025300203 28814235033917113537950305)
        ·
          refine ⟨21610676275437835153462729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28814235033917113537950305 21610676275437835153462729)
          ·
            refine ⟨16208007206578376365097047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21610676275437835153462729 16208007206578376365097047)
            ·
              refine ⟨24312010809867564547645571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16208007206578376365097047 24312010809867564547645571)
              ·
                refine ⟨36468016214801346821468357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24312010809867564547645571 36468016214801346821468357)
                ·
                  refine ⟨6837753040275252529025317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36468016214801346821468357 6837753040275252529025317)
                  ·
                    refine ⟨1282078695051609849192247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6837753040275252529025317 1282078695051609849192247)
                    ·
                      rfl

theorem cell23_7490518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_7490518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490518 prefixEnd_7490518 := by exact prefixLift 7490518
  have htrace : WordTrace (prefixWord ++ tailWord_7490518) baseStart_7490518 baseEnd_7490518 := by
    simpa [prefixWord, tailWord_7490518, baseEnd_7490518] using wordTrace_append hprefix tailTrace_7490518
  have hstable : (prefixWord ++ tailWord_7490518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490518).length < 2 ^ (prefixWord ++ tailWord_7490518).sum := by decide
  have hdescent : baseEnd_7490518 < baseStart_7490518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490525 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_7490525 : Nat := 118140960795 + 7490525 * 2 ^ 59
def prefixEnd_7490525 : Nat := 4983230072969 + 3 ^ 40 * 7490525 * 2
def baseEnd_7490525 : Nat := 3846239679519411020189209

theorem tailTrace_7490525 : CollatzResearch.WordTrace tailWord_7490525 prefixEnd_7490525 3846239679519411020189209 := by
  unfold tailWord_7490525
  simp only [CollatzResearch.WordTrace]
  refine ⟨273201891188114679666441029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182134594125409786444294019 273201891188114679666441029)
  ·
    refine ⟨51225354597771502437457693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273201891188114679666441029 51225354597771502437457693)
    ·
      refine ⟨19209507974164313414046635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51225354597771502437457693 19209507974164313414046635)
      ·
        refine ⟨28814261961246470121069953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19209507974164313414046635 28814261961246470121069953)
        ·
          refine ⟨21610696470934852590802465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28814261961246470121069953 21610696470934852590802465)
          ·
            refine ⟨16208022353201139443101849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21610696470934852590802465 16208022353201139443101849)
            ·
              refine ⟨12156016764900854582326387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16208022353201139443101849 12156016764900854582326387)
              ·
                refine ⟨18234025147351281873489581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12156016764900854582326387 18234025147351281873489581)
                ·
                  refine ⟨6837759430256730702558593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18234025147351281873489581 6837759430256730702558593)
                  ·
                    refine ⟨5128319572692548026918945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6837759430256730702558593 5128319572692548026918945)
                    ·
                      refine ⟨3846239679519411020189209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5128319572692548026918945 3846239679519411020189209)
                      ·
                        rfl

theorem cell23_7490525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_7490525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490525 prefixEnd_7490525 := by exact prefixLift 7490525
  have htrace : WordTrace (prefixWord ++ tailWord_7490525) baseStart_7490525 baseEnd_7490525 := by
    simpa [prefixWord, tailWord_7490525, baseEnd_7490525] using wordTrace_append hprefix tailTrace_7490525
  have hstable : (prefixWord ++ tailWord_7490525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490525).length < 2 ^ (prefixWord ++ tailWord_7490525).sum := by decide
  have hdescent : baseEnd_7490525 < baseStart_7490525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490537 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 6, 2, 5]
def baseStart_7490537 : Nat := 118140960795 + 7490537 * 2 ^ 59
def prefixEnd_7490537 : Nat := 4983230072969 + 3 ^ 40 * 7490537 * 2
def baseEnd_7490537 : Nat := 3846245841287264973239153

theorem tailTrace_7490537 : CollatzResearch.WordTrace tailWord_7490537 prefixEnd_7490537 3846245841287264973239153 := by
  unfold tailWord_7490537
  simp only [CollatzResearch.WordTrace]
  refine ⟨273202328864071205715877865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182134885909380803810585243 273202328864071205715877865)
  ·
    refine ⟨204901746648053404286908399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273202328864071205715877865 204901746648053404286908399)
    ·
      refine ⟨307352619972080106430362599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204901746648053404286908399 307352619972080106430362599)
      ·
        refine ⟨461028929958120159645543899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307352619972080106430362599 461028929958120159645543899)
        ·
          refine ⟨691543394937180239468315849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461028929958120159645543899 691543394937180239468315849)
          ·
            refine ⟨518657546202885179601236887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691543394937180239468315849 518657546202885179601236887)
            ·
              refine ⟨777986319304327769401855331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518657546202885179601236887 777986319304327769401855331)
              ·
                refine ⟨1166979478956491654102782997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777986319304327769401855331 1166979478956491654102782997)
                ·
                  refine ⟨54702163076085546286067953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1166979478956491654102782997 54702163076085546286067953)
                  ·
                    refine ⟨41026622307064159714550965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54702163076085546286067953 41026622307064159714550965)
                    ·
                      refine ⟨3846245841287264973239153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41026622307064159714550965 3846245841287264973239153)
                      ·
                        rfl

theorem cell23_7490537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_7490537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490537 prefixEnd_7490537 := by exact prefixLift 7490537
  have htrace : WordTrace (prefixWord ++ tailWord_7490537) baseStart_7490537 baseEnd_7490537 := by
    simpa [prefixWord, tailWord_7490537, baseEnd_7490537] using wordTrace_append hprefix tailTrace_7490537
  have hstable : (prefixWord ++ tailWord_7490537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490537).length < 2 ^ (prefixWord ++ tailWord_7490537).sum := by decide
  have hdescent : baseEnd_7490537 < baseStart_7490537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490568 : List Nat := [2, 1, 3, 2, 1, 3, 2, 3, 1, 3, 2]
def baseStart_7490568 : Nat := 118140960795 + 7490568 * 2 ^ 59
def prefixEnd_7490568 : Nat := 4983230072969 + 3 ^ 40 * 7490568 * 2
def baseEnd_7490568 : Nat := 3846261759187554351951511

theorem tailTrace_7490568 : CollatzResearch.WordTrace tailWord_7490568 prefixEnd_7490568 3846261759187554351951511 := by
  unfold tailWord_7490568
  simp only [CollatzResearch.WordTrace]
  refine ⟨136601729763479449005128179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182135639684639265340170905 136601729763479449005128179)
  ·
    refine ⟨204902594645219173507692269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136601729763479449005128179 204902594645219173507692269)
    ·
      refine ⟨76838472991957190065384601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204902594645219173507692269 76838472991957190065384601)
      ·
        refine ⟨57628854743967892549038451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76838472991957190065384601 57628854743967892549038451)
        ·
          refine ⟨86443282115951838823557677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57628854743967892549038451 86443282115951838823557677)
          ·
            refine ⟨32416230793481939558834129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86443282115951838823557677 32416230793481939558834129)
            ·
              refine ⟨24312173095111454669125597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32416230793481939558834129 24312173095111454669125597)
              ·
                refine ⟨9117064910666795500922099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24312173095111454669125597 9117064910666795500922099)
                ·
                  refine ⟨13675597366000193251383149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9117064910666795500922099 13675597366000193251383149)
                  ·
                    refine ⟨5128349012250072469268681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13675597366000193251383149 5128349012250072469268681)
                    ·
                      refine ⟨3846261759187554351951511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5128349012250072469268681 3846261759187554351951511)
                      ·
                        rfl

theorem cell23_7490568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_7490568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490568 prefixEnd_7490568 := by exact prefixLift 7490568
  have htrace : WordTrace (prefixWord ++ tailWord_7490568) baseStart_7490568 baseEnd_7490568 := by
    simpa [prefixWord, tailWord_7490568, baseEnd_7490568] using wordTrace_append hprefix tailTrace_7490568
  have hstable : (prefixWord ++ tailWord_7490568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490568).length < 2 ^ (prefixWord ++ tailWord_7490568).sum := by decide
  have hdescent : baseEnd_7490568 < baseStart_7490568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490602 : List Nat := [3, 1, 4, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_7490602 : Nat := 118140960795 + 7490602 * 2 ^ 59
def prefixEnd_7490602 : Nat := 4983230072969 + 3 ^ 40 * 7490602 * 2
def baseEnd_7490602 : Nat := 3846279217529807218926355

theorem tailTrace_7490602 : CollatzResearch.WordTrace tailWord_7490602 prefixEnd_7490602 3846279217529807218926355 := by
  unfold tailWord_7490602
  simp only [CollatzResearch.WordTrace]
  refine ⟨68301174902208930454248515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182136466405890481211329373 68301174902208930454248515)
  ·
    refine ⟨102451762353313395681372773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68301174902208930454248515 102451762353313395681372773)
    ·
      refine ⟨19209705441246261690257395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102451762353313395681372773 19209705441246261690257395)
      ·
        refine ⟨28814558161869392535386093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19209705441246261690257395 28814558161869392535386093)
        ·
          refine ⟨10805459310701022200769785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28814558161869392535386093 10805459310701022200769785)
          ·
            refine ⟨8104094483025766650577339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10805459310701022200769785 8104094483025766650577339)
            ·
              refine ⟨12156141724538649975866009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8104094483025766650577339 12156141724538649975866009)
              ·
                refine ⟨9117106293403987481899507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12156141724538649975866009 9117106293403987481899507)
                ·
                  refine ⟨13675659440105981222849261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9117106293403987481899507 13675659440105981222849261)
                  ·
                    refine ⟨5128372290039742958568473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13675659440105981222849261 5128372290039742958568473)
                    ·
                      refine ⟨3846279217529807218926355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5128372290039742958568473 3846279217529807218926355)
                      ·
                        rfl

theorem cell23_7490602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_7490602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490602 prefixEnd_7490602 := by exact prefixLift 7490602
  have htrace : WordTrace (prefixWord ++ tailWord_7490602) baseStart_7490602 baseEnd_7490602 := by
    simpa [prefixWord, tailWord_7490602, baseEnd_7490602] using wordTrace_append hprefix tailTrace_7490602
  have hstable : (prefixWord ++ tailWord_7490602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490602).length < 2 ^ (prefixWord ++ tailWord_7490602).sum := by decide
  have hdescent : baseEnd_7490602 < baseStart_7490602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490641 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 2, 5, 2]
def baseStart_7490641 : Nat := 118140960795 + 7490641 * 2 ^ 59
def prefixEnd_7490641 : Nat := 4983230072969 + 3 ^ 40 * 7490641 * 2
def baseEnd_7490641 : Nat := 3846299243275332566338675

theorem tailTrace_7490641 : CollatzResearch.WordTrace tailWord_7490641 prefixEnd_7490641 3846299243275332566338675 := by
  unfold tailWord_7490641
  simp only [CollatzResearch.WordTrace]
  refine ⟨273206122055694431477663777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182137414703796287651775851 273206122055694431477663777)
  ·
    refine ⟨204904591541770823608247833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273206122055694431477663777 204904591541770823608247833)
    ·
      refine ⟨153678443656328117706185875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204904591541770823608247833 153678443656328117706185875)
      ·
        refine ⟨230517665484492176559278813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153678443656328117706185875 230517665484492176559278813)
        ·
          refine ⟨86444124556684566209729555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230517665484492176559278813 86444124556684566209729555)
          ·
            refine ⟨129666186835026849314594333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86444124556684566209729555 129666186835026849314594333)
            ·
              refine ⟨48624820063135068492972875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129666186835026849314594333 48624820063135068492972875)
              ·
                refine ⟨72937230094702602739459313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48624820063135068492972875 72937230094702602739459313)
                ·
                  refine ⟨54702922571026952054594485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72937230094702602739459313 54702922571026952054594485)
                  ·
                    refine ⟨5128398991033776755118233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54702922571026952054594485 5128398991033776755118233)
                    ·
                      refine ⟨3846299243275332566338675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5128398991033776755118233 3846299243275332566338675)
                      ·
                        rfl

theorem cell23_7490641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 5, 2].length) (baseStart_7490641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490641 prefixEnd_7490641 := by exact prefixLift 7490641
  have htrace : WordTrace (prefixWord ++ tailWord_7490641) baseStart_7490641 baseEnd_7490641 := by
    simpa [prefixWord, tailWord_7490641, baseEnd_7490641] using wordTrace_append hprefix tailTrace_7490641
  have hstable : (prefixWord ++ tailWord_7490641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490641).length < 2 ^ (prefixWord ++ tailWord_7490641).sum := by decide
  have hdescent : baseEnd_7490641 < baseStart_7490641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490671 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 1, 6, 2]
def baseStart_7490671 : Nat := 118140960795 + 7490671 * 2 ^ 59
def prefixEnd_7490671 : Nat := 4983230072969 + 3 ^ 40 * 7490671 * 2
def baseEnd_7490671 : Nat := 3846314647694967448963537

theorem tailTrace_7490671 : CollatzResearch.WordTrace tailWord_7490671 prefixEnd_7490671 3846314647694967448963537 := by
  unfold tailWord_7490671
  simp only [CollatzResearch.WordTrace]
  refine ⟨273207216245585746601255867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182138144163723831067503911 273207216245585746601255867)
  ·
    refine ⟨409810824368378619901883801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273207216245585746601255867 409810824368378619901883801)
    ·
      refine ⟨307358118276283964926412851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409810824368378619901883801 307358118276283964926412851)
      ·
        refine ⟨461037177414425947389619277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307358118276283964926412851 461037177414425947389619277)
        ·
          refine ⟨172888941530409730271107229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461037177414425947389619277 172888941530409730271107229)
          ·
            refine ⟨64833353073903648851665211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172888941530409730271107229 64833353073903648851665211)
            ·
              refine ⟨97250029610855473277497817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64833353073903648851665211 97250029610855473277497817)
              ·
                refine ⟨72937522208141604958123363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97250029610855473277497817 72937522208141604958123363)
                ·
                  refine ⟨109406283312212407437185045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72937522208141604958123363 109406283312212407437185045)
                  ·
                    refine ⟨5128419530259956598618049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109406283312212407437185045 5128419530259956598618049)
                    ·
                      refine ⟨3846314647694967448963537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5128419530259956598618049 3846314647694967448963537)
                      ·
                        rfl

theorem cell23_7490671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 6, 2].length) (baseStart_7490671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490671 prefixEnd_7490671 := by exact prefixLift 7490671
  have htrace : WordTrace (prefixWord ++ tailWord_7490671) baseStart_7490671 baseEnd_7490671 := by
    simpa [prefixWord, tailWord_7490671, baseEnd_7490671] using wordTrace_append hprefix tailTrace_7490671
  have hstable : (prefixWord ++ tailWord_7490671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490671).length < 2 ^ (prefixWord ++ tailWord_7490671).sum := by decide
  have hdescent : baseEnd_7490671 < baseStart_7490671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490684 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_7490684 : Nat := 118140960795 + 7490684 * 2 ^ 59
def prefixEnd_7490684 : Nat := 4983230072969 + 3 ^ 40 * 7490684 * 2
def baseEnd_7490684 : Nat := 3846321322943475898100977

theorem tailTrace_7490684 : CollatzResearch.WordTrace tailWord_7490684 prefixEnd_7490684 3846321322943475898100977 := by
  unfold tailWord_7490684
  simp only [CollatzResearch.WordTrace]
  refine ⟨136603845197269324910739553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182138460263025766547652737 136603845197269324910739553)
  ·
    refine ⟨102452883897951993683054665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136603845197269324910739553 102452883897951993683054665)
    ·
      refine ⟨76839662923463995262290999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102452883897951993683054665 76839662923463995262290999)
      ·
        refine ⟨115259494385195992893436499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76839662923463995262290999 115259494385195992893436499)
        ·
          refine ⟨172889241577793989340154749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115259494385195992893436499 172889241577793989340154749)
          ·
            refine ⟨64833465591672746002558031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172889241577793989340154749 64833465591672746002558031)
            ·
              refine ⟨97250198387509119003837047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64833465591672746002558031 97250198387509119003837047)
              ·
                refine ⟨145875297581263678505755571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97250198387509119003837047 145875297581263678505755571)
                ·
                  refine ⟨218812946371895517758633357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145875297581263678505755571 218812946371895517758633357)
                  ·
                    refine ⟨82054854889460819159487509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218812946371895517758633357 82054854889460819159487509)
                    ·
                      refine ⟨3846321322943475898100977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82054854889460819159487509 3846321322943475898100977)
                      ·
                        rfl

theorem cell23_7490684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_7490684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490684 prefixEnd_7490684 := by exact prefixLift 7490684
  have htrace : WordTrace (prefixWord ++ tailWord_7490684) baseStart_7490684 baseEnd_7490684 := by
    simpa [prefixWord, tailWord_7490684, baseEnd_7490684] using wordTrace_append hprefix tailTrace_7490684
  have hstable : (prefixWord ++ tailWord_7490684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490684).length < 2 ^ (prefixWord ++ tailWord_7490684).sum := by decide
  have hdescent : baseEnd_7490684 < baseStart_7490684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490691 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 3]
def baseStart_7490691 : Nat := 118140960795 + 7490691 * 2 ^ 59
def prefixEnd_7490691 : Nat := 4983230072969 + 3 ^ 40 * 7490691 * 2
def baseEnd_7490691 : Nat := 3846324917308057370713445

theorem tailTrace_7490691 : CollatzResearch.WordTrace tailWord_7490691 prefixEnd_7490691 3846324917308057370713445 := by
  unfold tailWord_7490691
  simp only [CollatzResearch.WordTrace]
  refine ⟨273207945705513290016983927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182138630470342193344655951 273207945705513290016983927)
  ·
    refine ⟨409811918558269935025475891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273207945705513290016983927 409811918558269935025475891)
    ·
      refine ⟨614717877837404902538213837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409811918558269935025475891 614717877837404902538213837)
      ·
        refine ⟨230519204189026838451830189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 614717877837404902538213837 230519204189026838451830189)
        ·
          refine ⟨86444701570885064419436321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230519204189026838451830189 86444701570885064419436321)
          ·
            refine ⟨64833526178163798314577241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86444701570885064419436321 64833526178163798314577241)
            ·
              refine ⟨48625144633622848735932931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64833526178163798314577241 48625144633622848735932931)
              ·
                refine ⟨72937716950434273103899397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48625144633622848735932931 72937716950434273103899397)
                ·
                  refine ⟨13675821928206426206981137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72937716950434273103899397 13675821928206426206981137)
                  ·
                    refine ⟨10256866446154819655235853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13675821928206426206981137 10256866446154819655235853)
                    ·
                      refine ⟨3846324917308057370713445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10256866446154819655235853 3846324917308057370713445)
                      ·
                        rfl

theorem cell23_7490691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_7490691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490691 prefixEnd_7490691 := by exact prefixLift 7490691
  have htrace : WordTrace (prefixWord ++ tailWord_7490691) baseStart_7490691 baseEnd_7490691 := by
    simpa [prefixWord, tailWord_7490691, baseEnd_7490691] using wordTrace_append hprefix tailTrace_7490691
  have hstable : (prefixWord ++ tailWord_7490691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490691).length < 2 ^ (prefixWord ++ tailWord_7490691).sum := by decide
  have hdescent : baseEnd_7490691 < baseStart_7490691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490698 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 3, 4]
def baseStart_7490698 : Nat := 118140960795 + 7490698 * 2 ^ 59
def prefixEnd_7490698 : Nat := 4983230072969 + 3 ^ 40 * 7490698 * 2
def baseEnd_7490698 : Nat := 1282109503890879614441971

theorem tailTrace_7490698 : CollatzResearch.WordTrace tailWord_7490698 prefixEnd_7490698 1282109503890879614441971 := by
  unfold tailWord_7490698
  simp only [CollatzResearch.WordTrace]
  refine ⟨68302050254121982553122187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182138800677658620141659165 68302050254121982553122187)
  ·
    refine ⟨102453075381182973829683281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68302050254121982553122187 102453075381182973829683281)
    ·
      refine ⟨76839806535887230372262461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102453075381182973829683281 76839806535887230372262461)
      ·
        refine ⟨28814927450957711389598423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76839806535887230372262461 28814927450957711389598423)
        ·
          refine ⟨43222391176436567084397635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28814927450957711389598423 43222391176436567084397635)
          ·
            refine ⟨64833586764654850626596453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43222391176436567084397635 64833586764654850626596453)
            ·
              refine ⟨12156297518372784492486835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64833586764654850626596453 12156297518372784492486835)
              ·
                refine ⟨18234446277559176738730253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12156297518372784492486835 18234446277559176738730253)
                ·
                  refine ⟨6837917354084691277023845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18234446277559176738730253 6837917354084691277023845)
                  ·
                    refine ⟨1282109503890879614441971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6837917354084691277023845 1282109503890879614441971)
                    ·
                      rfl

theorem cell23_7490698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_7490698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490698 prefixEnd_7490698 := by exact prefixLift 7490698
  have htrace : WordTrace (prefixWord ++ tailWord_7490698) baseStart_7490698 baseEnd_7490698 := by
    simpa [prefixWord, tailWord_7490698, baseEnd_7490698] using wordTrace_append hprefix tailTrace_7490698
  have hstable : (prefixWord ++ tailWord_7490698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490698).length < 2 ^ (prefixWord ++ tailWord_7490698).sum := by decide
  have hdescent : baseEnd_7490698 < baseStart_7490698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490721 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_7490721 : Nat := 118140960795 + 7490721 * 2 ^ 59
def prefixEnd_7490721 : Nat := 4983230072969 + 3 ^ 40 * 7490721 * 2
def baseEnd_7490721 : Nat := 3846340321727692253338307

theorem tailTrace_7490721 : CollatzResearch.WordTrace tailWord_7490721 prefixEnd_7490721 3846340321727692253338307 := by
  unfold tailWord_7490721
  simp only [CollatzResearch.WordTrace]
  refine ⟨273209039895404605140576017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182139359930269736760384011 273209039895404605140576017)
  ·
    refine ⟨204906779921553453855432013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273209039895404605140576017 204906779921553453855432013)
    ·
      refine ⟨76840042470582545195787005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204906779921553453855432013 76840042470582545195787005)
      ·
        refine ⟨28815015926468454448420127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76840042470582545195787005 28815015926468454448420127)
        ·
          refine ⟨43222523889702681672630191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28815015926468454448420127 43222523889702681672630191)
          ·
            refine ⟨64833785834554022508945287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43222523889702681672630191 64833785834554022508945287)
            ·
              refine ⟨97250678751831033763417931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64833785834554022508945287 97250678751831033763417931)
              ·
                refine ⟨145876018127746550645126897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97250678751831033763417931 145876018127746550645126897)
                ·
                  refine ⟨109407013595809912983845173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145876018127746550645126897 109407013595809912983845173)
                  ·
                    refine ⟨10256907524607179342235485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109407013595809912983845173 10256907524607179342235485)
                    ·
                      refine ⟨3846340321727692253338307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10256907524607179342235485 3846340321727692253338307)
                      ·
                        rfl

theorem cell23_7490721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_7490721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490721 prefixEnd_7490721 := by exact prefixLift 7490721
  have htrace : WordTrace (prefixWord ++ tailWord_7490721) baseStart_7490721 baseEnd_7490721 := by
    simpa [prefixWord, tailWord_7490721, baseEnd_7490721] using wordTrace_append hprefix tailTrace_7490721
  have hstable : (prefixWord ++ tailWord_7490721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490721).length < 2 ^ (prefixWord ++ tailWord_7490721).sum := by decide
  have hdescent : baseEnd_7490721 < baseStart_7490721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490795 : List Nat := [1, 1, 1, 1, 2, 7, 3, 1, 1, 1, 4]
def baseStart_7490795 : Nat := 118140960795 + 7490795 * 2 ^ 59
def prefixEnd_7490795 : Nat := 4983230072969 + 3 ^ 40 * 7490795 * 2
def baseEnd_7490795 : Nat := 3846378319296124963812967

theorem tailTrace_7490795 : CollatzResearch.WordTrace tailWord_7490795 prefixEnd_7490795 3846378319296124963812967 := by
  unfold tailWord_7490795
  simp only [CollatzResearch.WordTrace]
  refine ⟨273211738897136515778769839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182141159264757677185846559 273211738897136515778769839)
  ·
    refine ⟨409817608345704773668154759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273211738897136515778769839 409817608345704773668154759)
    ·
      refine ⟨614726412518557160502232139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409817608345704773668154759 614726412518557160502232139)
      ·
        refine ⟨922089618777835740753348209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614726412518557160502232139 922089618777835740753348209)
        ·
          refine ⟨691567214083376805565011157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922089618777835740753348209 691567214083376805565011157)
          ·
            refine ⟨16208606580079143880429949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 691567214083376805565011157 16208606580079143880429949)
            ·
              refine ⟨6078227467529678955161231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16208606580079143880429949 6078227467529678955161231)
              ·
                refine ⟨9117341201294518432741847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6078227467529678955161231 9117341201294518432741847)
                ·
                  refine ⟨13676011801941777649112771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9117341201294518432741847 13676011801941777649112771)
                  ·
                    refine ⟨20514017702912666473669157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13676011801941777649112771 20514017702912666473669157)
                    ·
                      refine ⟨3846378319296124963812967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20514017702912666473669157 3846378319296124963812967)
                      ·
                        rfl

theorem cell23_7490795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 1, 1, 4].length) (baseStart_7490795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490795 prefixEnd_7490795 := by exact prefixLift 7490795
  have htrace : WordTrace (prefixWord ++ tailWord_7490795) baseStart_7490795 baseEnd_7490795 := by
    simpa [prefixWord, tailWord_7490795, baseEnd_7490795] using wordTrace_append hprefix tailTrace_7490795
  have hstable : (prefixWord ++ tailWord_7490795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490795).length < 2 ^ (prefixWord ++ tailWord_7490795).sum := by decide
  have hdescent : baseEnd_7490795 < baseStart_7490795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490798 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_7490798 : Nat := 118140960795 + 7490798 * 2 ^ 59
def prefixEnd_7490798 : Nat := 4983230072969 + 3 ^ 40 * 7490798 * 2
def baseEnd_7490798 : Nat := 3846379859738088452075453

theorem tailTrace_7490798 : CollatzResearch.WordTrace tailWord_7490798 prefixEnd_7490798 3846379859738088452075453 := by
  unfold tailWord_7490798
  simp only [CollatzResearch.WordTrace]
  refine ⟨34151481039515705911391131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182141232210750431527419365 34151481039515705911391131)
  ·
    refine ⟨51227221559273558867086697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34151481039515705911391131 51227221559273558867086697)
    ·
      refine ⟨38420416169455169150315023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51227221559273558867086697 38420416169455169150315023)
      ·
        refine ⟨57630624254182753725472535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38420416169455169150315023 57630624254182753725472535)
        ·
          refine ⟨86445936381274130588208803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57630624254182753725472535 86445936381274130588208803)
          ·
            refine ⟨129668904571911195882313205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86445936381274130588208803 129668904571911195882313205)
            ·
              refine ⟨12156459803616674613966863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129668904571911195882313205 12156459803616674613966863)
              ·
                refine ⟨18234689705425011920950295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12156459803616674613966863 18234689705425011920950295)
                ·
                  refine ⟨27352034558137517881425443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18234689705425011920950295 27352034558137517881425443)
                  ·
                    refine ⟨41028051837206276822138165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27352034558137517881425443 41028051837206276822138165)
                    ·
                      refine ⟨3846379859738088452075453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41028051837206276822138165 3846379859738088452075453)
                      ·
                        rfl

theorem cell23_7490798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_7490798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490798 prefixEnd_7490798 := by exact prefixLift 7490798
  have htrace : WordTrace (prefixWord ++ tailWord_7490798) baseStart_7490798 baseEnd_7490798 := by
    simpa [prefixWord, tailWord_7490798, baseEnd_7490798] using wordTrace_append hprefix tailTrace_7490798
  have hstable : (prefixWord ++ tailWord_7490798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490798).length < 2 ^ (prefixWord ++ tailWord_7490798).sum := by decide
  have hdescent : baseEnd_7490798 < baseStart_7490798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490828 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 1, 3, 3]
def baseStart_7490828 : Nat := 118140960795 + 7490828 * 2 ^ 59
def prefixEnd_7490828 : Nat := 4983230072969 + 3 ^ 40 * 7490828 * 2
def baseEnd_7490828 : Nat := 3846395264157723334700315

theorem tailTrace_7490828 : CollatzResearch.WordTrace tailWord_7490828 prefixEnd_7490828 3846395264157723334700315 := by
  unfold tailWord_7490828
  simp only [CollatzResearch.WordTrace]
  refine ⟨136606471253008481207360569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182141961670677974943147425 136606471253008481207360569)
  ·
    refine ⟨102454853439756360905520427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136606471253008481207360569 102454853439756360905520427)
    ·
      refine ⟨153682280159634541358280641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102454853439756360905520427 153682280159634541358280641)
      ·
        refine ⟨115261710119725906018710481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153682280159634541358280641 115261710119725906018710481)
        ·
          refine ⟨86446282589794429514032861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115261710119725906018710481 86446282589794429514032861)
          ·
            refine ⟨32417355971172911067762323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86446282589794429514032861 32417355971172911067762323)
            ·
              refine ⟨48626033956759366601643485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32417355971172911067762323 48626033956759366601643485)
              ·
                refine ⟨18234762733784762475616307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48626033956759366601643485 18234762733784762475616307)
                ·
                  refine ⟨27352144100677143713424461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18234762733784762475616307 27352144100677143713424461)
                  ·
                    refine ⟨10257054037753928892534173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27352144100677143713424461 10257054037753928892534173)
                    ·
                      refine ⟨3846395264157723334700315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10257054037753928892534173 3846395264157723334700315)
                      ·
                        rfl

theorem cell23_7490828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_7490828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490828 prefixEnd_7490828 := by exact prefixLift 7490828
  have htrace : WordTrace (prefixWord ++ tailWord_7490828) baseStart_7490828 baseEnd_7490828 := by
    simpa [prefixWord, tailWord_7490828, baseEnd_7490828] using wordTrace_append hprefix tailTrace_7490828
  have hstable : (prefixWord ++ tailWord_7490828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490828).length < 2 ^ (prefixWord ++ tailWord_7490828).sum := by decide
  have hdescent : baseEnd_7490828 < baseStart_7490828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490845 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_7490845 : Nat := 118140960795 + 7490845 * 2 ^ 59
def prefixEnd_7490845 : Nat := 4983230072969 + 3 ^ 40 * 7490845 * 2
def baseEnd_7490845 : Nat := 3846403993328849768187737

theorem tailTrace_7490845 : CollatzResearch.WordTrace tailWord_7490845 prefixEnd_7490845 3846403993328849768187737 := by
  unfold tailWord_7490845
  simp only [CollatzResearch.WordTrace]
  refine ⟨273213562546955374318089989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182142375031303582878726659 273213562546955374318089989)
  ·
    refine ⟨51227542977554132684641873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273213562546955374318089989 51227542977554132684641873)
    ·
      refine ⟨38420657233165599513481405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51227542977554132684641873 38420657233165599513481405)
      ·
        refine ⟨14407746462437099817555527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38420657233165599513481405 14407746462437099817555527)
        ·
          refine ⟨21611619693655649726333291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14407746462437099817555527 21611619693655649726333291)
          ·
            refine ⟨32417429540483474589499937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21611619693655649726333291 32417429540483474589499937)
            ·
              refine ⟨24313072155362605942124953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32417429540483474589499937 24313072155362605942124953)
              ·
                refine ⟨18234804116521954456593715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24313072155362605942124953 18234804116521954456593715)
                ·
                  refine ⟨27352206174782931684890573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18234804116521954456593715 27352206174782931684890573)
                  ·
                    refine ⟨10257077315543599381833965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27352206174782931684890573 10257077315543599381833965)
                    ·
                      refine ⟨3846403993328849768187737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10257077315543599381833965 3846403993328849768187737)
                      ·
                        rfl

theorem cell23_7490845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_7490845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490845 prefixEnd_7490845 := by exact prefixLift 7490845
  have htrace : WordTrace (prefixWord ++ tailWord_7490845) baseStart_7490845 baseEnd_7490845 := by
    simpa [prefixWord, tailWord_7490845, baseEnd_7490845] using wordTrace_append hprefix tailTrace_7490845
  have hstable : (prefixWord ++ tailWord_7490845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490845).length < 2 ^ (prefixWord ++ tailWord_7490845).sum := by decide
  have hdescent : baseEnd_7490845 < baseStart_7490845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490846 : List Nat := [4, 3, 2, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_7490846 : Nat := 118140960795 + 7490846 * 2 ^ 59
def prefixEnd_7490846 : Nat := 4983230072969 + 3 ^ 40 * 7490846 * 2
def baseEnd_7490846 : Nat := 3846404506809504264275233

theorem tailTrace_7490846 : CollatzResearch.WordTrace tailWord_7490846 prefixEnd_7490846 3846404506809504264275233 := by
  unfold tailWord_7490846
  simp only [CollatzResearch.WordTrace]
  refine ⟨34151699877493968936109549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182142399346634500992584261 34151699877493968936109549)
  ·
    refine ⟨12806887454060238351041081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34151699877493968936109549 12806887454060238351041081)
    ·
      refine ⟨9605165590545178763280811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12806887454060238351041081 9605165590545178763280811)
      ·
        refine ⟨14407748385817768144921217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9605165590545178763280811 14407748385817768144921217)
        ·
          refine ⟨10805811289363326108690913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14407748385817768144921217 10805811289363326108690913)
          ·
            refine ⟨8104358467022494581518185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10805811289363326108690913 8104358467022494581518185)
            ·
              refine ⟨6078268850266870936138639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8104358467022494581518185 6078268850266870936138639)
              ·
                refine ⟨9117403275400306404207959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6078268850266870936138639 9117403275400306404207959)
                ·
                  refine ⟨13676104913100459606311939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9117403275400306404207959 13676104913100459606311939)
                  ·
                    refine ⟨20514157369650689409467909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13676104913100459606311939 20514157369650689409467909)
                    ·
                      refine ⟨3846404506809504264275233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20514157369650689409467909 3846404506809504264275233)
                      ·
                        rfl

theorem cell23_7490846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_7490846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490846 prefixEnd_7490846 := by exact prefixLift 7490846
  have htrace : WordTrace (prefixWord ++ tailWord_7490846) baseStart_7490846 baseEnd_7490846 := by
    simpa [prefixWord, tailWord_7490846, baseEnd_7490846] using wordTrace_append hprefix tailTrace_7490846
  have hstable : (prefixWord ++ tailWord_7490846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490846).length < 2 ^ (prefixWord ++ tailWord_7490846).sum := by decide
  have hdescent : baseEnd_7490846 < baseStart_7490846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490871 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_7490871 : Nat := 118140960795 + 7490871 * 2 ^ 59
def prefixEnd_7490871 : Nat := 4983230072969 + 3 ^ 40 * 7490871 * 2
def baseEnd_7490871 : Nat := 3846417343825866666462617

theorem tailTrace_7490871 : CollatzResearch.WordTrace tailWord_7490871 prefixEnd_7490871 3846417343825866666462617 := by
  unfold tailWord_7490871
  simp only [CollatzResearch.WordTrace]
  refine ⟨273214510844861180758536467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182143007229907453839024311 273214510844861180758536467)
  ·
    refine ⟨409821766267291771137804701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273214510844861180758536467 409821766267291771137804701)
    ·
      refine ⟨153683162350234414176676763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409821766267291771137804701 153683162350234414176676763)
      ·
        refine ⟨230524743525351621265015145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153683162350234414176676763 230524743525351621265015145)
        ·
          refine ⟨172893557644013715948761359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230524743525351621265015145 172893557644013715948761359)
          ·
            refine ⟨259340336466020573923142039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172893557644013715948761359 259340336466020573923142039)
            ·
              refine ⟨389010504699030860884713059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259340336466020573923142039 389010504699030860884713059)
              ·
                refine ⟨583515757048546291327069589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389010504699030860884713059 583515757048546291327069589)
                ·
                  refine ⟨27352301111650607405956387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 583515757048546291327069589 27352301111650607405956387)
                  ·
                    refine ⟨41028451667475911108934581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27352301111650607405956387 41028451667475911108934581)
                    ·
                      refine ⟨3846417343825866666462617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41028451667475911108934581 3846417343825866666462617)
                      ·
                        rfl

theorem cell23_7490871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_7490871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490871 prefixEnd_7490871 := by exact prefixLift 7490871
  have htrace : WordTrace (prefixWord ++ tailWord_7490871) baseStart_7490871 baseEnd_7490871 := by
    simpa [prefixWord, tailWord_7490871, baseEnd_7490871] using wordTrace_append hprefix tailTrace_7490871
  have hstable : (prefixWord ++ tailWord_7490871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490871).length < 2 ^ (prefixWord ++ tailWord_7490871).sum := by decide
  have hdescent : baseEnd_7490871 < baseStart_7490871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490878 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_7490878 : Nat := 118140960795 + 7490878 * 2 ^ 59
def prefixEnd_7490878 : Nat := 4983230072969 + 3 ^ 40 * 7490878 * 2
def baseEnd_7490878 : Nat := 1282140312730149379691695

theorem tailTrace_7490878 : CollatzResearch.WordTrace tailWord_7490878 prefixEnd_7490878 1282140312730149379691695 := by
  unfold tailWord_7490878
  simp only [CollatzResearch.WordTrace]
  refine ⟨34151845769479477619255161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182143177437223880636027525 34151845769479477619255161)
  ·
    refine ⟨25613884327109608214441371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34151845769479477619255161 25613884327109608214441371)
    ·
      refine ⟨38420826490664412321662057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25613884327109608214441371 38420826490664412321662057)
      ·
        refine ⟨28815619867998309241246543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38420826490664412321662057 28815619867998309241246543)
        ·
          refine ⟨43223429801997463861869815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28815619867998309241246543 43223429801997463861869815)
          ·
            refine ⟨64835144702996195792804723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43223429801997463861869815 64835144702996195792804723)
            ·
              refine ⟨97252717054494293689207085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64835144702996195792804723 97252717054494293689207085)
              ·
                refine ⟨36469768895435360133452657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97252717054494293689207085 36469768895435360133452657)
                ·
                  refine ⟨27352326671576520100089493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36469768895435360133452657 27352326671576520100089493)
                  ·
                    refine ⟨1282140312730149379691695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27352326671576520100089493 1282140312730149379691695)
                    ·
                      rfl

theorem cell23_7490878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_7490878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490878 prefixEnd_7490878 := by exact prefixLift 7490878
  have htrace : WordTrace (prefixWord ++ tailWord_7490878) baseStart_7490878 baseEnd_7490878 := by
    simpa [prefixWord, tailWord_7490878, baseEnd_7490878] using wordTrace_append hprefix tailTrace_7490878
  have hstable : (prefixWord ++ tailWord_7490878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490878).length < 2 ^ (prefixWord ++ tailWord_7490878).sum := by decide
  have hdescent : baseEnd_7490878 < baseStart_7490878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490886 : List Nat := [6, 1, 1, 3, 2, 1, 2, 7]
def baseStart_7490886 : Nat := 118140960795 + 7490886 * 2 ^ 59
def prefixEnd_7490886 : Nat := 4983230072969 + 3 ^ 40 * 7490886 * 2
def baseEnd_7490886 : Nat := 142460186890210522510187

theorem tailTrace_7490886 : CollatzResearch.WordTrace tailWord_7490886 prefixEnd_7490886 142460186890210522510187 := by
  unfold tailWord_7490886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8537970560618963697510391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182143371959871225546888341 8537970560618963697510391)
  ·
    refine ⟨12806955840928445546265587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8537970560618963697510391 12806955840928445546265587)
    ·
      refine ⟨19210433761392668319398381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12806955840928445546265587 19210433761392668319398381)
      ·
        refine ⟨7203912660522250619774393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19210433761392668319398381 7203912660522250619774393)
        ·
          refine ⟨5402934495391687964830795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7203912660522250619774393 5402934495391687964830795)
          ·
            refine ⟨8104401743087531947246193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5402934495391687964830795 8104401743087531947246193)
            ·
              refine ⟨6078301307315648960434645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8104401743087531947246193 6078301307315648960434645)
              ·
                refine ⟨142460186890210522510187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6078301307315648960434645 142460186890210522510187)
                ·
                  rfl

theorem cell23_7490886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_7490886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490886 prefixEnd_7490886 := by exact prefixLift 7490886
  have htrace : WordTrace (prefixWord ++ tailWord_7490886) baseStart_7490886 baseEnd_7490886 := by
    simpa [prefixWord, tailWord_7490886, baseEnd_7490886] using wordTrace_append hprefix tailTrace_7490886
  have hstable : (prefixWord ++ tailWord_7490886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490886).length < 2 ^ (prefixWord ++ tailWord_7490886).sum := by decide
  have hdescent : baseEnd_7490886 < baseStart_7490886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490921 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 3, 7]
def baseStart_7490921 : Nat := 118140960795 + 7490921 * 2 ^ 59
def prefixEnd_7490921 : Nat := 4983230072969 + 3 ^ 40 * 7490921 * 2
def baseEnd_7490921 : Nat := 1282147672619530490279129

theorem tailTrace_7490921 : CollatzResearch.WordTrace tailWord_7490921 prefixEnd_7490921 1282147672619530490279129 := by
  unfold tailWord_7490921
  simp only [CollatzResearch.WordTrace]
  refine ⟨273216334494680039297856617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182144222996453359531904411 273216334494680039297856617)
  ·
    refine ⟨204912250871010029473392463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273216334494680039297856617 204912250871010029473392463)
    ·
      refine ⟨307368376306515044210088695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204912250871010029473392463 307368376306515044210088695)
      ·
        refine ⟨461052564459772566315133043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307368376306515044210088695 461052564459772566315133043)
        ·
          refine ⟨691578846689658849472699565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461052564459772566315133043 691578846689658849472699565)
          ·
            refine ⟨259342067508622068552262337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 691578846689658849472699565 259342067508622068552262337)
            ·
              refine ⟨194506550631466551414196753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259342067508622068552262337 194506550631466551414196753)
              ·
                refine ⟨145879912973599913560647565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194506550631466551414196753 145879912973599913560647565)
                ·
                  refine ⟨54704967365099967585242837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145879912973599913560647565 54704967365099967585242837)
                  ·
                    refine ⟨1282147672619530490279129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54704967365099967585242837 1282147672619530490279129)
                    ·
                      rfl

theorem cell23_7490921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_7490921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490921 prefixEnd_7490921 := by exact prefixLift 7490921
  have htrace : WordTrace (prefixWord ++ tailWord_7490921) baseStart_7490921 baseEnd_7490921 := by
    simpa [prefixWord, tailWord_7490921, baseEnd_7490921] using wordTrace_append hprefix tailTrace_7490921
  have hstable : (prefixWord ++ tailWord_7490921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490921).length < 2 ^ (prefixWord ++ tailWord_7490921).sum := by decide
  have hdescent : baseEnd_7490921 < baseStart_7490921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490925 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 7]
def baseStart_7490925 : Nat := 118140960795 + 7490925 * 2 ^ 59
def prefixEnd_7490925 : Nat := 4983230072969 + 3 ^ 40 * 7490925 * 2
def baseEnd_7490925 : Nat := 427382785753467717243041

theorem tailTrace_7490925 : CollatzResearch.WordTrace tailWord_7490925 prefixEnd_7490925 427382785753467717243041 := by
  unfold tailWord_7490925
  simp only [CollatzResearch.WordTrace]
  refine ⟨273216480386665547981002229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182144320257777031987334819 273216480386665547981002229)
  ·
    refine ⟨25614045036249895123218959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273216480386665547981002229 25614045036249895123218959)
    ·
      refine ⟨38421067554374842684828439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25614045036249895123218959 38421067554374842684828439)
      ·
        refine ⟨57631601331562264027242659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38421067554374842684828439 57631601331562264027242659)
        ·
          refine ⟨86447401997343396040863989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57631601331562264027242659 86447401997343396040863989)
          ·
            refine ⟨8104443937250943378830999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86447401997343396040863989 8104443937250943378830999)
            ·
              refine ⟨12156665905876415068246499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8104443937250943378830999 12156665905876415068246499)
              ·
                refine ⟨18234998858814622602369749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12156665905876415068246499 18234998858814622602369749)
                ·
                  refine ⟨427382785753467717243041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18234998858814622602369749 427382785753467717243041)
                  ·
                    rfl

theorem cell23_7490925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_7490925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490925 prefixEnd_7490925 := by exact prefixLift 7490925
  have htrace : WordTrace (prefixWord ++ tailWord_7490925) baseStart_7490925 baseEnd_7490925 := by
    simpa [prefixWord, tailWord_7490925, baseEnd_7490925] using wordTrace_append hprefix tailTrace_7490925
  have hstable : (prefixWord ++ tailWord_7490925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490925).length < 2 ^ (prefixWord ++ tailWord_7490925).sum := by decide
  have hdescent : baseEnd_7490925 < baseStart_7490925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7490975 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 4]
def baseStart_7490975 : Nat := 118140960795 + 7490975 * 2 ^ 59
def prefixEnd_7490975 : Nat := 4983230072969 + 3 ^ 40 * 7490975 * 2
def baseEnd_7490975 : Nat := 3846470745813934259562139

theorem tailTrace_7490975 : CollatzResearch.WordTrace tailWord_7490975 prefixEnd_7490975 3846470745813934259562139 := by
  unfold tailWord_7490975
  simp only [CollatzResearch.WordTrace]
  refine ⟨273218304036484406520322379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182145536024322937680214919 273218304036484406520322379)
  ·
    refine ⟨409827456054726609780483569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273218304036484406520322379 409827456054726609780483569)
    ·
      refine ⟨307370592041044957335362677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409827456054726609780483569 307370592041044957335362677)
      ·
        refine ⟨28815993003847964750190251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 307370592041044957335362677 28815993003847964750190251)
        ·
          refine ⟨43223989505771947125285377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28815993003847964750190251 43223989505771947125285377)
          ·
            refine ⟨32417992129328960343964033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43223989505771947125285377 32417992129328960343964033)
            ·
              refine ⟨24313494096996720257973025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32417992129328960343964033 24313494096996720257973025)
              ·
                refine ⟨18235120572747540193479769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24313494096996720257973025 18235120572747540193479769)
                ·
                  refine ⟨13676340429560655145109827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18235120572747540193479769 13676340429560655145109827)
                  ·
                    refine ⟨20514510644340982717664741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13676340429560655145109827 20514510644340982717664741)
                    ·
                      refine ⟨3846470745813934259562139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20514510644340982717664741 3846470745813934259562139)
                      ·
                        rfl

theorem cell23_7490975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_7490975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7490975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7490975 prefixEnd_7490975 := by exact prefixLift 7490975
  have htrace : WordTrace (prefixWord ++ tailWord_7490975) baseStart_7490975 baseEnd_7490975 := by
    simpa [prefixWord, tailWord_7490975, baseEnd_7490975] using wordTrace_append hprefix tailTrace_7490975
  have hstable : (prefixWord ++ tailWord_7490975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7490975).length < 2 ^ (prefixWord ++ tailWord_7490975).sum := by decide
  have hdescent : baseEnd_7490975 < baseStart_7490975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7490975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491012 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_7491012 : Nat := 118140960795 + 7491012 * 2 ^ 59
def prefixEnd_7491012 : Nat := 4983230072969 + 3 ^ 40 * 7491012 * 2
def baseEnd_7491012 : Nat := 3846489744598150614799469

theorem tailTrace_7491012 : CollatzResearch.WordTrace tailWord_7491012 prefixEnd_7491012 3846489744598150614799469 := by
  unfold tailWord_7491012
  simp only [CollatzResearch.WordTrace]
  refine ⟨136609826768675180919709645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182146435691566907892946193 136609826768675180919709645)
  ·
    refine ⟨51228685038253192844891117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136609826768675180919709645 51228685038253192844891117)
    ·
      refine ⟨19210756889344947316834169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51228685038253192844891117 19210756889344947316834169)
      ·
        refine ⟨14408067667008710487625627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19210756889344947316834169 14408067667008710487625627)
        ·
          refine ⟨21612101500513065731438441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14408067667008710487625627 21612101500513065731438441)
          ·
            refine ⟨16209076125384799298578831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21612101500513065731438441 16209076125384799298578831)
            ·
              refine ⟨24313614188077198947868247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16209076125384799298578831 24313614188077198947868247)
              ·
                refine ⟨36470421282115798421802371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24313614188077198947868247 36470421282115798421802371)
                ·
                  refine ⟨54705631923173697632703557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36470421282115798421802371 54705631923173697632703557)
                  ·
                    refine ⟨10257305985595068306131917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54705631923173697632703557 10257305985595068306131917)
                    ·
                      refine ⟨3846489744598150614799469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10257305985595068306131917 3846489744598150614799469)
                      ·
                        rfl

theorem cell23_7491012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_7491012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491012 prefixEnd_7491012 := by exact prefixLift 7491012
  have htrace : WordTrace (prefixWord ++ tailWord_7491012) baseStart_7491012 baseEnd_7491012 := by
    simpa [prefixWord, tailWord_7491012, baseEnd_7491012] using wordTrace_append hprefix tailTrace_7491012
  have hstable : (prefixWord ++ tailWord_7491012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491012).length < 2 ^ (prefixWord ++ tailWord_7491012).sum := by decide
  have hdescent : baseEnd_7491012 < baseStart_7491012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491062 : List Nat := [5, 1, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_7491062 : Nat := 118140960795 + 7491062 * 2 ^ 59
def prefixEnd_7491062 : Nat := 4983230072969 + 3 ^ 40 * 7491062 * 2
def baseEnd_7491062 : Nat := 1282171806210291806391413

theorem tailTrace_7491062 : CollatzResearch.WordTrace tailWord_7491062 prefixEnd_7491062 1282171806210291806391413 := by
  unfold tailWord_7491062
  simp only [CollatzResearch.WordTrace]
  refine ⟨17076342324198076273671215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182147651458112813585826293 17076342324198076273671215)
  ·
    refine ⟨25614513486297114410506823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17076342324198076273671215 25614513486297114410506823)
    ·
      refine ⟨38421770229445671615760235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25614513486297114410506823 38421770229445671615760235)
      ·
        refine ⟨57632655344168507423640353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38421770229445671615760235 57632655344168507423640353)
        ·
          refine ⟨43224491508126380567730265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57632655344168507423640353 43224491508126380567730265)
          ·
            refine ⟨32418368631094785425797699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43224491508126380567730265 32418368631094785425797699)
            ·
              refine ⟨48627552946642178138696549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32418368631094785425797699 48627552946642178138696549)
              ·
                refine ⟨9117666177495408401005603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48627552946642178138696549 9117666177495408401005603)
                ·
                  refine ⟨13676499266243112601508405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9117666177495408401005603 13676499266243112601508405)
                  ·
                    refine ⟨1282171806210291806391413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13676499266243112601508405 1282171806210291806391413)
                    ·
                      rfl

theorem cell23_7491062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_7491062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491062 prefixEnd_7491062 := by exact prefixLift 7491062
  have htrace : WordTrace (prefixWord ++ tailWord_7491062) baseStart_7491062 baseEnd_7491062 := by
    simpa [prefixWord, tailWord_7491062, baseEnd_7491062] using wordTrace_append hprefix tailTrace_7491062
  have hstable : (prefixWord ++ tailWord_7491062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491062).length < 2 ^ (prefixWord ++ tailWord_7491062).sum := by decide
  have hdescent : baseEnd_7491062 < baseStart_7491062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491065 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 1, 8, 2]
def baseStart_7491065 : Nat := 118140960795 + 7491065 * 2 ^ 59
def prefixEnd_7491065 : Nat := 4983230072969 + 3 ^ 40 * 7491065 * 2
def baseEnd_7491065 : Nat := 3846516959072838907436725

theorem tailTrace_7491065 : CollatzResearch.WordTrace tailWord_7491065 prefixEnd_7491065 3846516959072838907436725 := by
  unfold tailWord_7491065
  simp only [CollatzResearch.WordTrace]
  refine ⟨273221586606158351891098649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182147724404105567927399099 273221586606158351891098649)
  ·
    refine ⟨204916189954618763918323987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273221586606158351891098649 204916189954618763918323987)
    ·
      refine ⟨307374284931928145877485981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204916189954618763918323987 307374284931928145877485981)
      ·
        refine ⟨115265356849473054704057243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307374284931928145877485981 115265356849473054704057243)
        ·
          refine ⟨172898035274209582056085865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115265356849473054704057243 172898035274209582056085865)
          ·
            refine ⟨129673526455657186542064399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172898035274209582056085865 129673526455657186542064399)
            ·
              refine ⟨194510289683485779813096599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129673526455657186542064399 194510289683485779813096599)
              ·
                refine ⟨291765434525228669719644899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194510289683485779813096599 291765434525228669719644899)
                ·
                  refine ⟨437648151787843004579467349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291765434525228669719644899 437648151787843004579467349)
                  ·
                    refine ⟨5128689278763785209915633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 437648151787843004579467349 5128689278763785209915633)
                    ·
                      refine ⟨3846516959072838907436725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5128689278763785209915633 3846516959072838907436725)
                      ·
                        rfl

theorem cell23_7491065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_7491065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491065 prefixEnd_7491065 := by exact prefixLift 7491065
  have htrace : WordTrace (prefixWord ++ tailWord_7491065) baseStart_7491065 baseEnd_7491065 := by
    simpa [prefixWord, tailWord_7491065, baseEnd_7491065] using wordTrace_append hprefix tailTrace_7491065
  have hstable : (prefixWord ++ tailWord_7491065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491065).length < 2 ^ (prefixWord ++ tailWord_7491065).sum := by decide
  have hdescent : baseEnd_7491065 < baseStart_7491065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491070 : List Nat := [4, 2, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_7491070 : Nat := 118140960795 + 7491070 * 2 ^ 59
def prefixEnd_7491070 : Nat := 4983230072969 + 3 ^ 40 * 7491070 * 2
def baseEnd_7491070 : Nat := 1282173175492037129291401

theorem tailTrace_7491070 : CollatzResearch.WordTrace tailWord_7491070 prefixEnd_7491070 1282173175492037129291401 := by
  unfold tailWord_7491070
  simp only [CollatzResearch.WordTrace]
  refine ⟨34152721121392529718128833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182147845980760158496687109 34152721121392529718128833)
  ·
    refine ⟨25614540841044397288596625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34152721121392529718128833 25614540841044397288596625)
    ·
      refine ⟨19210905630783297966447469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25614540841044397288596625 19210905630783297966447469)
      ·
        refine ⟨7204089611543736737417801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19210905630783297966447469 7204089611543736737417801)
        ·
          refine ⟨5403067208657802553063351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7204089611543736737417801 5403067208657802553063351)
          ·
            refine ⟨8104600812986703829595027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5403067208657802553063351 8104600812986703829595027)
            ·
              refine ⟨12156901219480055744392541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8104600812986703829595027 12156901219480055744392541)
              ·
                refine ⟨4558837957305020904147203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12156901219480055744392541 4558837957305020904147203)
                ·
                  refine ⟨6838256935957531356220805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4558837957305020904147203 6838256935957531356220805)
                  ·
                    refine ⟨1282173175492037129291401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6838256935957531356220805 1282173175492037129291401)
                    ·
                      rfl

theorem cell23_7491070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_7491070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491070 prefixEnd_7491070 := by exact prefixLift 7491070
  have htrace : WordTrace (prefixWord ++ tailWord_7491070) baseStart_7491070 baseEnd_7491070 := by
    simpa [prefixWord, tailWord_7491070, baseEnd_7491070] using wordTrace_append hprefix tailTrace_7491070
  have hstable : (prefixWord ++ tailWord_7491070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491070).length < 2 ^ (prefixWord ++ tailWord_7491070).sum := by decide
  have hdescent : baseEnd_7491070 < baseStart_7491070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491082 : List Nat := [3, 1, 2, 2, 2, 2, 2, 3, 1, 1, 4]
def baseStart_7491082 : Nat := 118140960795 + 7491082 * 2 ^ 59
def prefixEnd_7491082 : Nat := 4983230072969 + 3 ^ 40 * 7491082 * 2
def baseEnd_7491082 : Nat := 3846525688243965340924147

theorem tailTrace_7491082 : CollatzResearch.WordTrace tailWord_7491082 prefixEnd_7491082 3846525688243965340924147 := by
  unfold tailWord_7491082
  simp only [CollatzResearch.WordTrace]
  refine ⟨68305551661774190948616875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182148137764731175862978333 68305551661774190948616875)
  ·
    refine ⟨102458327492661286422925313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68305551661774190948616875 102458327492661286422925313)
    ·
      refine ⟨76843745619495964817193985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102458327492661286422925313 76843745619495964817193985)
      ·
        refine ⟨57632809214621973612895489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76843745619495964817193985 57632809214621973612895489)
        ·
          refine ⟨43224606910966480209671617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57632809214621973612895489 43224606910966480209671617)
          ·
            refine ⟨32418455183224860157253713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43224606910966480209671617 32418455183224860157253713)
            ·
              refine ⟨24313841387418645117940285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32418455183224860157253713 24313841387418645117940285)
              ·
                refine ⟨9117690520281991919227607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24313841387418645117940285 9117690520281991919227607)
                ·
                  refine ⟨13676535780422987878841411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9117690520281991919227607 13676535780422987878841411)
                  ·
                    refine ⟨20514803670634481818262117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13676535780422987878841411 20514803670634481818262117)
                    ·
                      refine ⟨3846525688243965340924147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20514803670634481818262117 3846525688243965340924147)
                      ·
                        rfl

theorem cell23_7491082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_7491082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491082 prefixEnd_7491082 := by exact prefixLift 7491082
  have htrace : WordTrace (prefixWord ++ tailWord_7491082) baseStart_7491082 baseEnd_7491082 := by
    simpa [prefixWord, tailWord_7491082, baseEnd_7491082] using wordTrace_append hprefix tailTrace_7491082
  have hstable : (prefixWord ++ tailWord_7491082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491082).length < 2 ^ (prefixWord ++ tailWord_7491082).sum := by decide
  have hdescent : baseEnd_7491082 < baseStart_7491082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491105 : List Nat := [1, 2, 3, 2, 2, 3, 2, 8]
def baseStart_7491105 : Nat := 118140960795 + 7491105 * 2 ^ 59
def prefixEnd_7491105 : Nat := 4983230072969 + 3 ^ 40 * 7491105 * 2
def baseEnd_7491105 : Nat := 142464351788852546330983

theorem tailTrace_7491105 : CollatzResearch.WordTrace tailWord_7491105 prefixEnd_7491105 142464351788852546330983 := by
  unfold tailWord_7491105
  simp only [CollatzResearch.WordTrace]
  refine ⟨273223045526013438722554769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182148697017342292481703179 273223045526013438722554769)
  ·
    refine ⟨204917284144510079041916077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273223045526013438722554769 204917284144510079041916077)
    ·
      refine ⟨76843981554191279640718529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204917284144510079041916077 76843981554191279640718529)
      ·
        refine ⟨57632986165643459730538897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76843981554191279640718529 57632986165643459730538897)
        ·
          refine ⟨43224739624232594797904173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57632986165643459730538897 43224739624232594797904173)
          ·
            refine ⟨16209277359087223049214065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43224739624232594797904173 16209277359087223049214065)
            ·
              refine ⟨12156958019315417286910549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16209277359087223049214065 12156958019315417286910549)
              ·
                refine ⟨142464351788852546330983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12156958019315417286910549 142464351788852546330983)
                ·
                  rfl

theorem cell23_7491105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 8].length) (baseStart_7491105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491105 prefixEnd_7491105 := by exact prefixLift 7491105
  have htrace : WordTrace (prefixWord ++ tailWord_7491105) baseStart_7491105 baseEnd_7491105 := by
    simpa [prefixWord, tailWord_7491105, baseEnd_7491105] using wordTrace_append hprefix tailTrace_7491105
  have hstable : (prefixWord ++ tailWord_7491105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491105).length < 2 ^ (prefixWord ++ tailWord_7491105).sum := by decide
  have hdescent : baseEnd_7491105 < baseStart_7491105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491175 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_7491175 : Nat := 118140960795 + 7491175 * 2 ^ 59
def prefixEnd_7491175 : Nat := 4983230072969 + 3 ^ 40 * 7491175 * 2
def baseEnd_7491175 : Nat := 3846573441944833477061219

theorem tailTrace_7491175 : CollatzResearch.WordTrace tailWord_7491175 prefixEnd_7491175 3846573441944833477061219 := by
  unfold tailWord_7491175
  simp only [CollatzResearch.WordTrace]
  refine ⟨273225598635759840677602979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182150399090506560451735319 273225598635759840677602979)
  ·
    refine ⟨409838397953639761016404469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273225598635759840677602979 409838397953639761016404469)
    ·
      refine ⟨38422349808153727595287919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 409838397953639761016404469 38422349808153727595287919)
      ·
        refine ⟨57633524712230591392931879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38422349808153727595287919 57633524712230591392931879)
        ·
          refine ⟨86450287068345887089397819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57633524712230591392931879 86450287068345887089397819)
          ·
            refine ⟨129675430602518830634096729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86450287068345887089397819 129675430602518830634096729)
            ·
              refine ⟨97256572951889122975572547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129675430602518830634096729 97256572951889122975572547)
              ·
                refine ⟨145884859427833684463358821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97256572951889122975572547 145884859427833684463358821)
                ·
                  refine ⟨27353411142718815836879779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145884859427833684463358821 27353411142718815836879779)
                  ·
                    refine ⟨41030116714078223755319669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27353411142718815836879779 41030116714078223755319669)
                    ·
                      refine ⟨3846573441944833477061219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41030116714078223755319669 3846573441944833477061219)
                      ·
                        rfl

theorem cell23_7491175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_7491175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491175 prefixEnd_7491175 := by exact prefixLift 7491175
  have htrace : WordTrace (prefixWord ++ tailWord_7491175) baseStart_7491175 baseEnd_7491175 := by
    simpa [prefixWord, tailWord_7491175, baseEnd_7491175] using wordTrace_append hprefix tailTrace_7491175
  have hstable : (prefixWord ++ tailWord_7491175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491175).length < 2 ^ (prefixWord ++ tailWord_7491175).sum := by decide
  have hdescent : baseEnd_7491175 < baseStart_7491175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491212 : List Nat := [2, 2, 1, 2, 1, 1, 3, 6, 5]
def baseStart_7491212 : Nat := 118140960795 + 7491212 * 2 ^ 59
def prefixEnd_7491212 : Nat := 4983230072969 + 3 ^ 40 * 7491212 * 2
def baseEnd_7491212 : Nat := 427399160081005536922061

theorem tailTrace_7491212 : CollatzResearch.WordTrace tailWord_7491212 prefixEnd_7491212 427399160081005536922061 := by
  unfold tailWord_7491212
  simp only [CollatzResearch.WordTrace]
  refine ⟨136613474068312897998349945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182151298757750530664466593 136613474068312897998349945)
  ·
    refine ⟨102460105551234673498762459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136613474068312897998349945 102460105551234673498762459)
    ·
      refine ⟨153690158326852010248143689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102460105551234673498762459 153690158326852010248143689)
      ·
        refine ⟨115267618745139007686107767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153690158326852010248143689 115267618745139007686107767)
        ·
          refine ⟨172901428117708511529161651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115267618745139007686107767 172901428117708511529161651)
          ·
            refine ⟨259352142176562767293742477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172901428117708511529161651 259352142176562767293742477)
            ·
              refine ⟨97257053316211037735153429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259352142176562767293742477 97257053316211037735153429)
              ·
                refine ⟨4558924374197392393835317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97257053316211037735153429 4558924374197392393835317)
                ·
                  refine ⟨427399160081005536922061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4558924374197392393835317 427399160081005536922061)
                  ·
                    rfl

theorem cell23_7491212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 5].length) (baseStart_7491212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491212 prefixEnd_7491212 := by exact prefixLift 7491212
  have htrace : WordTrace (prefixWord ++ tailWord_7491212) baseStart_7491212 baseEnd_7491212 := by
    simpa [prefixWord, tailWord_7491212, baseEnd_7491212] using wordTrace_append hprefix tailTrace_7491212
  have hstable : (prefixWord ++ tailWord_7491212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491212).length < 2 ^ (prefixWord ++ tailWord_7491212).sum := by decide
  have hdescent : baseEnd_7491212 < baseStart_7491212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491223 : List Nat := [1, 1, 3, 3, 2, 3, 3, 1, 2, 2, 2]
def baseStart_7491223 : Nat := 118140960795 + 7491223 * 2 ^ 59
def prefixEnd_7491223 : Nat := 4983230072969 + 3 ^ 40 * 7491223 * 2
def baseEnd_7491223 : Nat := 3846598089016249289260999

theorem tailTrace_7491223 : CollatzResearch.WordTrace tailWord_7491223 prefixEnd_7491223 3846598089016249289260999 := by
  unfold tailWord_7491223
  simp only [CollatzResearch.WordTrace]
  refine ⟨273227349339585944875350323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182151566226390629916900215 273227349339585944875350323)
  ·
    refine ⟨409841024009378917313025485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273227349339585944875350323 409841024009378917313025485)
    ·
      refine ⟨153690384003517093992384557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409841024009378917313025485 153690384003517093992384557)
      ·
        refine ⟨57633894001318910247144209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153690384003517093992384557 57633894001318910247144209)
        ·
          refine ⟨43225420500989182685358157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57633894001318910247144209 43225420500989182685358157)
          ·
            refine ⟨16209532687870943507009309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43225420500989182685358157 16209532687870943507009309)
            ·
              refine ⟨6078574757951603815128491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16209532687870943507009309 6078574757951603815128491)
              ·
                refine ⟨9117862136927405722692737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6078574757951603815128491 9117862136927405722692737)
                ·
                  refine ⟨6838396602695554292019553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9117862136927405722692737 6838396602695554292019553)
                  ·
                    refine ⟨5128797452021665719014665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6838396602695554292019553 5128797452021665719014665)
                    ·
                      refine ⟨3846598089016249289260999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5128797452021665719014665 3846598089016249289260999)
                      ·
                        rfl

theorem cell23_7491223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_7491223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491223 prefixEnd_7491223 := by exact prefixLift 7491223
  have htrace : WordTrace (prefixWord ++ tailWord_7491223) baseStart_7491223 baseEnd_7491223 := by
    simpa [prefixWord, tailWord_7491223, baseEnd_7491223] using wordTrace_append hprefix tailTrace_7491223
  have hstable : (prefixWord ++ tailWord_7491223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491223).length < 2 ^ (prefixWord ++ tailWord_7491223).sum := by decide
  have hdescent : baseEnd_7491223 < baseStart_7491223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491225 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 6, 5]
def baseStart_7491225 : Nat := 118140960795 + 7491225 * 2 ^ 59
def prefixEnd_7491225 : Nat := 4983230072969 + 3 ^ 40 * 7491225 * 2
def baseEnd_7491225 : Nat := 1282199705325852760478663

theorem tailTrace_7491225 : CollatzResearch.WordTrace tailWord_7491225 prefixEnd_7491225 1282199705325852760478663 := by
  unfold tailWord_7491225
  simp only [CollatzResearch.WordTrace]
  refine ⟨273227422285578699216923129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182151614857052466144615419 273227422285578699216923129)
  ·
    refine ⟨204920566714184024412692347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273227422285578699216923129 204920566714184024412692347)
    ·
      refine ⟨307380850071276036619038521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204920566714184024412692347 307380850071276036619038521)
      ·
        refine ⟨230535637553457027464278891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307380850071276036619038521 230535637553457027464278891)
        ·
          refine ⟨345803456330185541196418337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230535637553457027464278891 345803456330185541196418337)
          ·
            refine ⟨259352592247639155897313753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345803456330185541196418337 259352592247639155897313753)
            ·
              refine ⟨194514444185729366922985315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259352592247639155897313753 194514444185729366922985315)
              ·
                refine ⟨291771666278594050384477973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194514444185729366922985315 291771666278594050384477973)
                ·
                  refine ⟨13676796856809096111772405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 291771666278594050384477973 13676796856809096111772405)
                  ·
                    refine ⟨1282199705325852760478663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13676796856809096111772405 1282199705325852760478663)
                    ·
                      rfl

theorem cell23_7491225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 5].length) (baseStart_7491225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491225 prefixEnd_7491225 := by exact prefixLift 7491225
  have htrace : WordTrace (prefixWord ++ tailWord_7491225) baseStart_7491225 baseEnd_7491225 := by
    simpa [prefixWord, tailWord_7491225, baseEnd_7491225] using wordTrace_append hprefix tailTrace_7491225
  have hstable : (prefixWord ++ tailWord_7491225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491225).length < 2 ^ (prefixWord ++ tailWord_7491225).sum := by decide
  have hdescent : baseEnd_7491225 < baseStart_7491225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491275 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 6]
def baseStart_7491275 : Nat := 118140960795 + 7491275 * 2 ^ 59
def prefixEnd_7491275 : Nat := 4983230072969 + 3 ^ 40 * 7491275 * 2
def baseEnd_7491275 : Nat := 3846624790010283085810759

theorem tailTrace_7491275 : CollatzResearch.WordTrace tailWord_7491275 prefixEnd_7491275 3846624790010283085810759 := by
  unfold tailWord_7491275
  simp only [CollatzResearch.WordTrace]
  refine ⟨273229245935397557756243279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182152830623598371837495519 273229245935397557756243279)
  ·
    refine ⟨409843868903096336634364919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273229245935397557756243279 409843868903096336634364919)
    ·
      refine ⟨614765803354644504951547379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409843868903096336634364919 614765803354644504951547379)
      ·
        refine ⟨922148705031966757427321069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614765803354644504951547379 922148705031966757427321069)
        ·
          refine ⟨345805764386987534035245401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 922148705031966757427321069 345805764386987534035245401)
          ·
            refine ⟨259354323290240650526434051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345805764386987534035245401 259354323290240650526434051)
            ·
              refine ⟨389031484935360975789651077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259354323290240650526434051 389031484935360975789651077)
              ·
                refine ⟨72943403425380182960559577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389031484935360975789651077 72943403425380182960559577)
                ·
                  refine ⟨54707552569035137220419683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72943403425380182960559577 54707552569035137220419683)
                  ·
                    refine ⟨82061328853552705830629525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54707552569035137220419683 82061328853552705830629525)
                    ·
                      refine ⟨3846624790010283085810759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82061328853552705830629525 3846624790010283085810759)
                      ·
                        rfl

theorem cell23_7491275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 6].length) (baseStart_7491275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491275 prefixEnd_7491275 := by exact prefixLift 7491275
  have htrace : WordTrace (prefixWord ++ tailWord_7491275) baseStart_7491275 baseEnd_7491275 := by
    simpa [prefixWord, tailWord_7491275, baseEnd_7491275] using wordTrace_append hprefix tailTrace_7491275
  have hstable : (prefixWord ++ tailWord_7491275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491275).length < 2 ^ (prefixWord ++ tailWord_7491275).sum := by decide
  have hdescent : baseEnd_7491275 < baseStart_7491275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491305 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 8]
def baseStart_7491305 : Nat := 118140960795 + 7491305 * 2 ^ 59
def prefixEnd_7491305 : Nat := 4983230072969 + 3 ^ 40 * 7491305 * 2
def baseEnd_7491305 : Nat := 3846640194429917968435621

theorem tailTrace_7491305 : CollatzResearch.WordTrace tailWord_7491305 prefixEnd_7491305 3846640194429917968435621 := by
  unfold tailWord_7491305
  simp only [CollatzResearch.WordTrace]
  refine ⟨273230340125288872879835369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182153560083525915253223579 273230340125288872879835369)
  ·
    refine ⟨204922755093966654659876527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273230340125288872879835369 204922755093966654659876527)
    ·
      refine ⟨307384132640949981989814791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204922755093966654659876527 307384132640949981989814791)
      ·
        refine ⟨461076198961424972984722187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307384132640949981989814791 461076198961424972984722187)
        ·
          refine ⟨691614298442137459477083281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461076198961424972984722187 691614298442137459477083281)
          ·
            refine ⟨518710723831603094607812461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691614298442137459477083281 518710723831603094607812461)
            ·
              refine ⟨194516521436851160477929673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 518710723831603094607812461 194516521436851160477929673)
              ·
                refine ⟨145887391077638370358447255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194516521436851160477929673 145887391077638370358447255)
                ·
                  refine ⟨218831086616457555537670883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145887391077638370358447255 218831086616457555537670883)
                  ·
                    refine ⟨328246629924686333306506325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218831086616457555537670883 328246629924686333306506325)
                    ·
                      refine ⟨3846640194429917968435621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 328246629924686333306506325 3846640194429917968435621)
                      ·
                        rfl

theorem cell23_7491305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_7491305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491305 prefixEnd_7491305 := by exact prefixLift 7491305
  have htrace : WordTrace (prefixWord ++ tailWord_7491305) baseStart_7491305 baseEnd_7491305 := by
    simpa [prefixWord, tailWord_7491305, baseEnd_7491305] using wordTrace_append hprefix tailTrace_7491305
  have hstable : (prefixWord ++ tailWord_7491305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491305).length < 2 ^ (prefixWord ++ tailWord_7491305).sum := by decide
  have hdescent : baseEnd_7491305 < baseStart_7491305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491339 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 4, 3, 2]
def baseStart_7491339 : Nat := 118140960795 + 7491339 * 2 ^ 59
def prefixEnd_7491339 : Nat := 4983230072969 + 3 ^ 40 * 7491339 * 2
def baseEnd_7491339 : Nat := 3846657652772170835410465

theorem tailTrace_7491339 : CollatzResearch.WordTrace tailWord_7491339 prefixEnd_7491339 3846657652772170835410465 := by
  unfold tailWord_7491339
  simp only [CollatzResearch.WordTrace]
  refine ⟨273231580207165696686573071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182154386804777131124382047 273231580207165696686573071)
  ·
    refine ⟨409847370310748545029859607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273231580207165696686573071 409847370310748545029859607)
    ·
      refine ⟨614771055466122817544789411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409847370310748545029859607 614771055466122817544789411)
      ·
        refine ⟨922156583199184226317184117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614771055466122817544789411 922156583199184226317184117)
        ·
          refine ⟨86452179674923521217236011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 922156583199184226317184117 86452179674923521217236011)
          ·
            refine ⟨129678269512385281825854017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86452179674923521217236011 129678269512385281825854017)
            ·
              refine ⟨97258702134288961369390513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129678269512385281825854017 97258702134288961369390513)
              ·
                refine ⟨72944026600716721027042885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97258702134288961369390513 72944026600716721027042885)
                ·
                  refine ⟨13677004987634385192570541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72944026600716721027042885 13677004987634385192570541)
                  ·
                    refine ⟨5128876870362894447213953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13677004987634385192570541 5128876870362894447213953)
                    ·
                      refine ⟨3846657652772170835410465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5128876870362894447213953 3846657652772170835410465)
                      ·
                        rfl

theorem cell23_7491339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 3, 2].length) (baseStart_7491339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491339 prefixEnd_7491339 := by exact prefixLift 7491339
  have htrace : WordTrace (prefixWord ++ tailWord_7491339) baseStart_7491339 baseEnd_7491339 := by
    simpa [prefixWord, tailWord_7491339, baseEnd_7491339] using wordTrace_append hprefix tailTrace_7491339
  have hstable : (prefixWord ++ tailWord_7491339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491339).length < 2 ^ (prefixWord ++ tailWord_7491339).sum := by decide
  have hdescent : baseEnd_7491339 < baseStart_7491339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491380 : List Nat := [2, 5, 1, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_7491380 : Nat := 118140960795 + 7491380 * 2 ^ 59
def prefixEnd_7491380 : Nat := 4983230072969 + 3 ^ 40 * 7491380 * 2
def baseEnd_7491380 : Nat := 3846678705479005174997777

theorem tailTrace_7491380 : CollatzResearch.WordTrace tailWord_7491380 prefixEnd_7491380 3846678705479005174997777 := by
  unfold tailWord_7491380
  simp only [CollatzResearch.WordTrace]
  refine ⟨136616537800008580344407797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182155383733344773792543729 136616537800008580344407797)
  ·
    refine ⟨12807800418750804407288231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136616537800008580344407797 12807800418750804407288231)
    ·
      refine ⟨19211700628126206610932347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12807800418750804407288231 19211700628126206610932347)
      ·
        refine ⟨28817550942189309916398521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19211700628126206610932347 28817550942189309916398521)
        ·
          refine ⟨21613163206641982437298891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28817550942189309916398521 21613163206641982437298891)
          ·
            refine ⟨32419744809962973655948337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21613163206641982437298891 32419744809962973655948337)
            ·
              refine ⟨24314808607472230241961253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32419744809962973655948337 24314808607472230241961253)
              ·
                refine ⟨4559026613901043170367735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24314808607472230241961253 4559026613901043170367735)
                ·
                  refine ⟨6838539920851564755551603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4559026613901043170367735 6838539920851564755551603)
                  ·
                    refine ⟨10257809881277347133327405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6838539920851564755551603 10257809881277347133327405)
                    ·
                      refine ⟨3846678705479005174997777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10257809881277347133327405 3846678705479005174997777)
                      ·
                        rfl

theorem cell23_7491380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_7491380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491380 prefixEnd_7491380 := by exact prefixLift 7491380
  have htrace : WordTrace (prefixWord ++ tailWord_7491380) baseStart_7491380 baseEnd_7491380 := by
    simpa [prefixWord, tailWord_7491380, baseEnd_7491380] using wordTrace_append hprefix tailTrace_7491380
  have hstable : (prefixWord ++ tailWord_7491380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491380).length < 2 ^ (prefixWord ++ tailWord_7491380).sum := by decide
  have hdescent : baseEnd_7491380 < baseStart_7491380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491389 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_7491389 : Nat := 118140960795 + 7491389 * 2 ^ 59
def prefixEnd_7491389 : Nat := 4983230072969 + 3 ^ 40 * 7491389 * 2
def baseEnd_7491389 : Nat := 3846683326804895639785235

theorem tailTrace_7491389 : CollatzResearch.WordTrace tailWord_7491389 prefixEnd_7491389 3846683326804895639785235 := by
  unfold tailWord_7491389
  simp only [CollatzResearch.WordTrace]
  refine ⟨273233403856984555225893221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182155602571323036817262147 273233403856984555225893221)
  ·
    refine ⟨51231263223184604104854979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273233403856984555225893221 51231263223184604104854979)
    ·
      refine ⟨76846894834776906157282469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51231263223184604104854979 76846894834776906157282469)
      ·
        refine ⟨14408792781520669904490463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76846894834776906157282469 14408792781520669904490463)
        ·
          refine ⟨21613189172281004856735695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14408792781520669904490463 21613189172281004856735695)
          ·
            refine ⟨32419783758421507285103543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21613189172281004856735695 32419783758421507285103543)
            ·
              refine ⟨48629675637632260927655315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32419783758421507285103543 48629675637632260927655315)
              ·
                refine ⟨72944513456448391391482973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48629675637632260927655315 72944513456448391391482973)
                ·
                  refine ⟨27354192546168146771806115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72944513456448391391482973 27354192546168146771806115)
                  ·
                    refine ⟨41031288819252220157709173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27354192546168146771806115 41031288819252220157709173)
                    ·
                      refine ⟨3846683326804895639785235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41031288819252220157709173 3846683326804895639785235)
                      ·
                        rfl

theorem cell23_7491389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_7491389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491389 prefixEnd_7491389 := by exact prefixLift 7491389
  have htrace : WordTrace (prefixWord ++ tailWord_7491389) baseStart_7491389 baseEnd_7491389 := by
    simpa [prefixWord, tailWord_7491389, baseEnd_7491389] using wordTrace_append hprefix tailTrace_7491389
  have hstable : (prefixWord ++ tailWord_7491389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491389).length < 2 ^ (prefixWord ++ tailWord_7491389).sum := by decide
  have hdescent : baseEnd_7491389 < baseStart_7491389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491399 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_7491399 : Nat := 118140960795 + 7491399 * 2 ^ 59
def prefixEnd_7491399 : Nat := 4983230072969 + 3 ^ 40 * 7491399 * 2
def baseEnd_7491399 : Nat := 3846688461611440600660189

theorem tailTrace_7491399 : CollatzResearch.WordTrace tailWord_7491399 prefixEnd_7491399 3846688461611440600660189 := by
  unfold tailWord_7491399
  simp only [CollatzResearch.WordTrace]
  refine ⟨273233768586948326933757251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182155845724632217955838167 273233768586948326933757251)
  ·
    refine ⟨409850652880422490400635877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273233768586948326933757251 409850652880422490400635877)
    ·
      refine ⟨76846997415079216950119227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409850652880422490400635877 76846997415079216950119227)
      ·
        refine ⟨115270496122618825425178841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76846997415079216950119227 115270496122618825425178841)
        ·
          refine ⟨86452872091964119068884131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115270496122618825425178841 86452872091964119068884131)
          ·
            refine ⟨129679308137946178603326197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86452872091964119068884131 129679308137946178603326197)
            ·
              refine ⟨12157435137932454244061831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129679308137946178603326197 12157435137932454244061831)
              ·
                refine ⟨18236152706898681366092747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12157435137932454244061831 18236152706898681366092747)
                ·
                  refine ⟨27354229060348022049139121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18236152706898681366092747 27354229060348022049139121)
                  ·
                    refine ⟨20515671795261016536854341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27354229060348022049139121 20515671795261016536854341)
                    ·
                      refine ⟨3846688461611440600660189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20515671795261016536854341 3846688461611440600660189)
                      ·
                        rfl

theorem cell23_7491399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_7491399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491399 prefixEnd_7491399 := by exact prefixLift 7491399
  have htrace : WordTrace (prefixWord ++ tailWord_7491399) baseStart_7491399 baseEnd_7491399 := by
    simpa [prefixWord, tailWord_7491399, baseEnd_7491399] using wordTrace_append hprefix tailTrace_7491399
  have hstable : (prefixWord ++ tailWord_7491399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491399).length < 2 ^ (prefixWord ++ tailWord_7491399).sum := by decide
  have hdescent : baseEnd_7491399 < baseStart_7491399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491409 : List Nat := [1, 2, 2, 1, 5, 1, 4, 7]
def baseStart_7491409 : Nat := 118140960795 + 7491409 * 2 ^ 59
def prefixEnd_7491409 : Nat := 4983230072969 + 3 ^ 40 * 7491409 * 2
def baseEnd_7491409 : Nat := 142470133200666131908709

theorem tailTrace_7491409 : CollatzResearch.WordTrace tailWord_7491409 prefixEnd_7491409 142470133200666131908709 := by
  unfold tailWord_7491409
  simp only [CollatzResearch.WordTrace]
  refine ⟨273234133316912098641621281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182156088877941399094414187 273234133316912098641621281)
  ·
    refine ⟨204925599987684073981215961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273234133316912098641621281 204925599987684073981215961)
    ·
      refine ⟨153694199990763055485911971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204925599987684073981215961 153694199990763055485911971)
      ·
        refine ⟨230541299986144583228867957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153694199990763055485911971 230541299986144583228867957)
        ·
          refine ⟨21613246873701054677706371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230541299986144583228867957 21613246873701054677706371)
          ·
            refine ⟨32419870310551582016559557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21613246873701054677706371 32419870310551582016559557)
            ·
              refine ⟨6078725683228421628104917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32419870310551582016559557 6078725683228421628104917)
              ·
                refine ⟨142470133200666131908709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6078725683228421628104917 142470133200666131908709)
                ·
                  rfl

theorem cell23_7491409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 7].length) (baseStart_7491409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491409 prefixEnd_7491409 := by exact prefixLift 7491409
  have htrace : WordTrace (prefixWord ++ tailWord_7491409) baseStart_7491409 baseEnd_7491409 := by
    simpa [prefixWord, tailWord_7491409, baseEnd_7491409] using wordTrace_append hprefix tailTrace_7491409
  have hstable : (prefixWord ++ tailWord_7491409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491409).length < 2 ^ (prefixWord ++ tailWord_7491409).sum := by decide
  have hdescent : baseEnd_7491409 < baseStart_7491409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491436 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 3]
def baseStart_7491436 : Nat := 118140960795 + 7491436 * 2 ^ 59
def prefixEnd_7491436 : Nat := 4983230072969 + 3 ^ 40 * 7491436 * 2
def baseEnd_7491436 : Nat := 3846707460395656955897519

theorem tailTrace_7491436 : CollatzResearch.WordTrace tailWord_7491436 prefixEnd_7491436 3846707460395656955897519 := by
  unfold tailWord_7491436
  simp only [CollatzResearch.WordTrace]
  refine ⟨136617559043907141126427081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182156745391876188168569441 136617559043907141126427081)
  ·
    refine ⟨102463169282930355844820311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136617559043907141126427081 102463169282930355844820311)
    ·
      refine ⟨153694753924395533767230467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102463169282930355844820311 153694753924395533767230467)
      ·
        refine ⟨230542130886593300650845701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153694753924395533767230467 230542130886593300650845701)
        ·
          refine ⟨43226649541236243872033569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230542130886593300650845701 43226649541236243872033569)
          ·
            refine ⟨32419987155927182904025177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43226649541236243872033569 32419987155927182904025177)
            ·
              refine ⟨24314990366945387178018883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32419987155927182904025177 24314990366945387178018883)
              ·
                refine ⟨36472485550418080767028325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24314990366945387178018883 36472485550418080767028325)
                ·
                  refine ⟨6838591040703390143817811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36472485550418080767028325 6838591040703390143817811)
                  ·
                    refine ⟨10257886561055085215726717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6838591040703390143817811 10257886561055085215726717)
                    ·
                      refine ⟨3846707460395656955897519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10257886561055085215726717 3846707460395656955897519)
                      ·
                        rfl

theorem cell23_7491436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_7491436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491436 prefixEnd_7491436 := by exact prefixLift 7491436
  have htrace : WordTrace (prefixWord ++ tailWord_7491436) baseStart_7491436 baseEnd_7491436 := by
    simpa [prefixWord, tailWord_7491436, baseEnd_7491436] using wordTrace_append hprefix tailTrace_7491436
  have hstable : (prefixWord ++ tailWord_7491436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491436).length < 2 ^ (prefixWord ++ tailWord_7491436).sum := by decide
  have hdescent : baseEnd_7491436 < baseStart_7491436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491457 : List Nat := [1, 2, 4, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_7491457 : Nat := 118140960795 + 7491457 * 2 ^ 59
def prefixEnd_7491457 : Nat := 4983230072969 + 3 ^ 40 * 7491457 * 2
def baseEnd_7491457 : Nat := 3846718243489401373734923

theorem tailTrace_7491457 : CollatzResearch.WordTrace tailWord_7491457 prefixEnd_7491457 3846718243489401373734923 := by
  unfold tailWord_7491457
  simp only [CollatzResearch.WordTrace]
  refine ⟨273235884020738202839368625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182157256013825468559579083 273235884020738202839368625)
  ·
    refine ⟨204926913015553652129526469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273235884020738202839368625 204926913015553652129526469)
    ·
      refine ⟨38423796190416309774286213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204926913015553652129526469 38423796190416309774286213)
      ·
        refine ⟨7204461785703058082678665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38423796190416309774286213 7204461785703058082678665)
        ·
          refine ⟨5403346339277293562008999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7204461785703058082678665 5403346339277293562008999)
          ·
            refine ⟨8105019508915940343013499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5403346339277293562008999 8105019508915940343013499)
            ·
              refine ⟨12157529263373910514520249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8105019508915940343013499 12157529263373910514520249)
              ·
                refine ⟨9118146947530432885890187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12157529263373910514520249 9118146947530432885890187)
                ·
                  refine ⟨13677220421295649328835281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9118146947530432885890187 13677220421295649328835281)
                  ·
                    refine ⟨10257915315971736996626461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13677220421295649328835281 10257915315971736996626461)
                    ·
                      refine ⟨3846718243489401373734923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10257915315971736996626461 3846718243489401373734923)
                      ·
                        rfl

theorem cell23_7491457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_7491457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491457 prefixEnd_7491457 := by exact prefixLift 7491457
  have htrace : WordTrace (prefixWord ++ tailWord_7491457) baseStart_7491457 baseEnd_7491457 := by
    simpa [prefixWord, tailWord_7491457, baseEnd_7491457] using wordTrace_append hprefix tailTrace_7491457
  have hstable : (prefixWord ++ tailWord_7491457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491457).length < 2 ^ (prefixWord ++ tailWord_7491457).sum := by decide
  have hdescent : baseEnd_7491457 < baseStart_7491457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491463 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 3, 3, 2]
def baseStart_7491463 : Nat := 118140960795 + 7491463 * 2 ^ 59
def prefixEnd_7491463 : Nat := 4983230072969 + 3 ^ 40 * 7491463 * 2
def baseEnd_7491463 : Nat := 3846721324373328350259895

theorem tailTrace_7491463 : CollatzResearch.WordTrace tailWord_7491463 prefixEnd_7491463 3846721324373328350259895 := by
  unfold tailWord_7491463
  simp only [CollatzResearch.WordTrace]
  refine ⟨273236102858716465864087043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182157401905810977242724695 273236102858716465864087043)
  ·
    refine ⟨409854154288074698796130565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273236102858716465864087043 409854154288074698796130565)
    ·
      refine ⟨76847653929014006024274481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409854154288074698796130565 76847653929014006024274481)
      ·
        refine ⟨57635740446760504518205861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76847653929014006024274481 57635740446760504518205861)
        ·
          refine ⟨10806701333767594597163599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57635740446760504518205861 10806701333767594597163599)
          ·
            refine ⟨16210052000651391895745399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10806701333767594597163599 16210052000651391895745399)
            ·
              refine ⟨24315078000977087843618099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16210052000651391895745399 24315078000977087843618099)
              ·
                refine ⟨36472617001465631765427149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24315078000977087843618099 36472617001465631765427149)
                ·
                  refine ⟨13677231375549611912035181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36472617001465631765427149 13677231375549611912035181)
                  ·
                    refine ⟨5128961765831104467013193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13677231375549611912035181 5128961765831104467013193)
                    ·
                      refine ⟨3846721324373328350259895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5128961765831104467013193 3846721324373328350259895)
                      ·
                        rfl

theorem cell23_7491463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_7491463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491463 prefixEnd_7491463 := by exact prefixLift 7491463
  have htrace : WordTrace (prefixWord ++ tailWord_7491463) baseStart_7491463 baseEnd_7491463 := by
    simpa [prefixWord, tailWord_7491463, baseEnd_7491463] using wordTrace_append hprefix tailTrace_7491463
  have hstable : (prefixWord ++ tailWord_7491463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491463).length < 2 ^ (prefixWord ++ tailWord_7491463).sum := by decide
  have hdescent : baseEnd_7491463 < baseStart_7491463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491479 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_7491479 : Nat := 118140960795 + 7491479 * 2 ^ 59
def prefixEnd_7491479 : Nat := 4983230072969 + 3 ^ 40 * 7491479 * 2
def baseEnd_7491479 : Nat := 3846729540063800287659821

theorem tailTrace_7491479 : CollatzResearch.WordTrace tailWord_7491479 prefixEnd_7491479 3846729540063800287659821 := by
  unfold tailWord_7491479
  simp only [CollatzResearch.WordTrace]
  refine ⟨273236686426658500596669491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182157790951105667064446327 273236686426658500596669491)
  ·
    refine ⟨409855029639987750895004237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273236686426658500596669491 409855029639987750895004237)
    ·
      refine ⟨153695636114995406585626589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409855029639987750895004237 153695636114995406585626589)
      ·
        refine ⟨57635863543123277469609971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153695636114995406585626589 57635863543123277469609971)
        ·
          refine ⟨86453795314684916204414957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57635863543123277469609971 86453795314684916204414957)
          ·
            refine ⟨32420173243006843576655609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86453795314684916204414957 32420173243006843576655609)
            ·
              refine ⟨24315129932255132682491707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32420173243006843576655609 24315129932255132682491707)
              ·
                refine ⟨36472694898382699023737561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24315129932255132682491707 36472694898382699023737561)
                ·
                  refine ⟨27354521173787024267803171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36472694898382699023737561 27354521173787024267803171)
                  ·
                    refine ⟨41031781760680536401704757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27354521173787024267803171 41031781760680536401704757)
                    ·
                      refine ⟨3846729540063800287659821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41031781760680536401704757 3846729540063800287659821)
                      ·
                        rfl

theorem cell23_7491479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_7491479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491479 prefixEnd_7491479 := by exact prefixLift 7491479
  have htrace : WordTrace (prefixWord ++ tailWord_7491479) baseStart_7491479 baseEnd_7491479 := by
    simpa [prefixWord, tailWord_7491479, baseEnd_7491479] using wordTrace_append hprefix tailTrace_7491479
  have hstable : (prefixWord ++ tailWord_7491479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491479).length < 2 ^ (prefixWord ++ tailWord_7491479).sum := by decide
  have hdescent : baseEnd_7491479 < baseStart_7491479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491566 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_7491566 : Nat := 118140960795 + 7491566 * 2 ^ 59
def prefixEnd_7491566 : Nat := 4983230072969 + 3 ^ 40 * 7491566 * 2
def baseEnd_7491566 : Nat := 3846774212880741447271921

theorem tailTrace_7491566 : CollatzResearch.WordTrace tailWord_7491566 prefixEnd_7491566 3846774212880741447271921 := by
  unfold tailWord_7491566
  simp only [CollatzResearch.WordTrace]
  refine ⟨34154982447167914306885819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182159906384895542970057701 34154982447167914306885819)
  ·
    refine ⟨51232473670751871460328729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34154982447167914306885819 51232473670751871460328729)
    ·
      refine ⟨38424355253063903595246547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51232473670751871460328729 38424355253063903595246547)
      ·
        refine ⟨57636532879595855392869821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38424355253063903595246547 57636532879595855392869821)
        ·
          refine ⟨21613699829848445772326183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57636532879595855392869821 21613699829848445772326183)
          ·
            refine ⟨32420549744772668658489275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21613699829848445772326183 32420549744772668658489275)
            ·
              refine ⟨48630824617159002987733913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32420549744772668658489275 48630824617159002987733913)
              ·
                refine ⟨36473118462869252240800435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48630824617159002987733913 36473118462869252240800435)
                ·
                  refine ⟨54709677694303878361200653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36473118462869252240800435 54709677694303878361200653)
                  ·
                    refine ⟨20516129135363954385450245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54709677694303878361200653 20516129135363954385450245)
                    ·
                      refine ⟨3846774212880741447271921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20516129135363954385450245 3846774212880741447271921)
                      ·
                        rfl

theorem cell23_7491566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_7491566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491566 prefixEnd_7491566 := by exact prefixLift 7491566
  have htrace : WordTrace (prefixWord ++ tailWord_7491566) baseStart_7491566 baseEnd_7491566 := by
    simpa [prefixWord, tailWord_7491566, baseEnd_7491566] using wordTrace_append hprefix tailTrace_7491566
  have hstable : (prefixWord ++ tailWord_7491566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491566).length < 2 ^ (prefixWord ++ tailWord_7491566).sum := by decide
  have hdescent : baseEnd_7491566 < baseStart_7491566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491576 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 3, 4]
def baseStart_7491576 : Nat := 118140960795 + 7491576 * 2 ^ 59
def prefixEnd_7491576 : Nat := 4983230072969 + 3 ^ 40 * 7491576 * 2
def baseEnd_7491576 : Nat := 1282259782562428802715625

theorem tailTrace_7491576 : CollatzResearch.WordTrace tailWord_7491576 prefixEnd_7491576 1282259782562428802715625 := by
  unfold tailWord_7491576
  simp only [CollatzResearch.WordTrace]
  refine ⟨136620112153653543081475291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182160149538204724108633721 136620112153653543081475291)
  ·
    refine ⟨204930168230480314622212937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136620112153653543081475291 204930168230480314622212937)
    ·
      refine ⟨153697626172860235966659703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204930168230480314622212937 153697626172860235966659703)
      ·
        refine ⟨230546439259290353949989555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153697626172860235966659703 230546439259290353949989555)
        ·
          refine ⟨345819658888935530924984333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230546439259290353949989555 345819658888935530924984333)
          ·
            refine ⟨129682372083350824096869125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345819658888935530924984333 129682372083350824096869125)
            ·
              refine ⟨24315444765628279518162961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129682372083350824096869125 24315444765628279518162961)
              ·
                refine ⟨18236583574221209638622221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24315444765628279518162961 18236583574221209638622221)
                ·
                  refine ⟨6838718840332953614483333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18236583574221209638622221 6838718840332953614483333)
                  ·
                    refine ⟨1282259782562428802715625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6838718840332953614483333 1282259782562428802715625)
                    ·
                      rfl

theorem cell23_7491576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_7491576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491576 prefixEnd_7491576 := by exact prefixLift 7491576
  have htrace : WordTrace (prefixWord ++ tailWord_7491576) baseStart_7491576 baseEnd_7491576 := by
    simpa [prefixWord, tailWord_7491576, baseEnd_7491576] using wordTrace_append hprefix tailTrace_7491576
  have hstable : (prefixWord ++ tailWord_7491576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491576).length < 2 ^ (prefixWord ++ tailWord_7491576).sum := by decide
  have hdescent : baseEnd_7491576 < baseStart_7491576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491589 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 8]
def baseStart_7491589 : Nat := 118140960795 + 7491589 * 2 ^ 59
def prefixEnd_7491589 : Nat := 4983230072969 + 3 ^ 40 * 7491589 * 2
def baseEnd_7491589 : Nat := 427420669215088317476035

theorem tailTrace_7491589 : CollatzResearch.WordTrace tailWord_7491589 prefixEnd_7491589 427420669215088317476035 := by
  unfold tailWord_7491589
  simp only [CollatzResearch.WordTrace]
  refine ⟨273240698456259989383173821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182160465637506659588782547 273240698456259989383173821)
  ·
    refine ⟨102465261921097496018690183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273240698456259989383173821 102465261921097496018690183)
    ·
      refine ⟨153697892881646244028035275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102465261921097496018690183 153697892881646244028035275)
      ·
        refine ⟨230546839322469366042052913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153697892881646244028035275 230546839322469366042052913)
        ·
          refine ⟨172910129491852024531539685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230546839322469366042052913 172910129491852024531539685)
          ·
            refine ⟨32420649279722254599663691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172910129491852024531539685 32420649279722254599663691)
            ·
              refine ⟨48630973919583381899495537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32420649279722254599663691 48630973919583381899495537)
              ·
                refine ⟨36473230439687536424621653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48630973919583381899495537 36473230439687536424621653)
                ·
                  refine ⟨427420669215088317476035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36473230439687536424621653 427420669215088317476035)
                  ·
                    rfl

theorem cell23_7491589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_7491589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491589 prefixEnd_7491589 := by exact prefixLift 7491589
  have htrace : WordTrace (prefixWord ++ tailWord_7491589) baseStart_7491589 baseEnd_7491589 := by
    simpa [prefixWord, tailWord_7491589, baseEnd_7491589] using wordTrace_append hprefix tailTrace_7491589
  have hstable : (prefixWord ++ tailWord_7491589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491589).length < 2 ^ (prefixWord ++ tailWord_7491589).sum := by decide
  have hdescent : baseEnd_7491589 < baseStart_7491589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491597 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_7491597 : Nat := 118140960795 + 7491597 * 2 ^ 59
def prefixEnd_7491597 : Nat := 4983230072969 + 3 ^ 40 * 7491597 * 2
def baseEnd_7491597 : Nat := 1282263376927010275328093

theorem tailTrace_7491597 : CollatzResearch.WordTrace tailWord_7491597 prefixEnd_7491597 1282263376927010275328093 := by
  unfold tailWord_7491597
  simp only [CollatzResearch.WordTrace]
  refine ⟨273240990240231006749465045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182160660160154004499643363 273240990240231006749465045)
  ·
    refine ⟨6404085708755414220690587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 273240990240231006749465045 6404085708755414220690587)
    ·
      refine ⟨9606128563133121331035881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6404085708755414220690587 9606128563133121331035881)
      ·
        refine ⟨7204596422349840998276911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9606128563133121331035881 7204596422349840998276911)
        ·
          refine ⟨10806894633524761497415367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7204596422349840998276911 10806894633524761497415367)
          ·
            refine ⟨16210341950287142246123051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10806894633524761497415367 16210341950287142246123051)
            ·
              refine ⟨24315512925430713369184577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16210341950287142246123051 24315512925430713369184577)
              ·
                refine ⟨18236634694073035026888433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24315512925430713369184577 18236634694073035026888433)
                ·
                  refine ⟨13677476020554776270166325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18236634694073035026888433 13677476020554776270166325)
                  ·
                    refine ⟨1282263376927010275328093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13677476020554776270166325 1282263376927010275328093)
                    ·
                      rfl

theorem cell23_7491597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_7491597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491597 prefixEnd_7491597 := by exact prefixLift 7491597
  have htrace : WordTrace (prefixWord ++ tailWord_7491597) baseStart_7491597 baseEnd_7491597 := by
    simpa [prefixWord, tailWord_7491597, baseEnd_7491597] using wordTrace_append hprefix tailTrace_7491597
  have hstable : (prefixWord ++ tailWord_7491597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491597).length < 2 ^ (prefixWord ++ tailWord_7491597).sum := by decide
  have hdescent : baseEnd_7491597 < baseStart_7491597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491670 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_7491670 : Nat := 118140960795 + 7491670 * 2 ^ 59
def prefixEnd_7491670 : Nat := 4983230072969 + 3 ^ 40 * 7491670 * 2
def baseEnd_7491670 : Nat := 1282275871622936346790481

theorem tailTrace_7491670 : CollatzResearch.WordTrace tailWord_7491670 prefixEnd_7491670 1282275871622936346790481 := by
  unfold tailWord_7491670
  simp only [CollatzResearch.WordTrace]
  refine ⟨17077728298060408763554529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182162435179311026811248309 17077728298060408763554529)
  ·
    refine ⟨12808296223545306572665897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17077728298060408763554529 12808296223545306572665897)
    ·
      refine ⟨9606222167658979929499423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12808296223545306572665897 9606222167658979929499423)
      ·
        refine ⟨14409333251488469894249135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9606222167658979929499423 14409333251488469894249135)
        ·
          refine ⟨21613999877232704841373703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14409333251488469894249135 21613999877232704841373703)
          ·
            refine ⟨32420999815849057262060555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21613999877232704841373703 32420999815849057262060555)
            ·
              refine ⟨48631499723773585893090833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32420999815849057262060555 48631499723773585893090833)
              ·
                refine ⟨36473624792830189419818125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48631499723773585893090833 36473624792830189419818125)
                ·
                  refine ⟨13677609297311321032431797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36473624792830189419818125 13677609297311321032431797)
                  ·
                    refine ⟨1282275871622936346790481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13677609297311321032431797 1282275871622936346790481)
                    ·
                      rfl

theorem cell23_7491670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_7491670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491670 prefixEnd_7491670 := by exact prefixLift 7491670
  have htrace : WordTrace (prefixWord ++ tailWord_7491670) baseStart_7491670 baseEnd_7491670 := by
    simpa [prefixWord, tailWord_7491670, baseEnd_7491670] using wordTrace_append hprefix tailTrace_7491670
  have hstable : (prefixWord ++ tailWord_7491670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491670).length < 2 ^ (prefixWord ++ tailWord_7491670).sum := by decide
  have hdescent : baseEnd_7491670 < baseStart_7491670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491679 : List Nat := [1, 1, 2, 3, 1, 1, 2, 12]
def baseStart_7491679 : Nat := 118140960795 + 7491679 * 2 ^ 59
def prefixEnd_7491679 : Nat := 4983230072969 + 3 ^ 40 * 7491679 * 2
def baseEnd_7491679 : Nat := 142475268007211092783663

theorem tailTrace_7491679 : CollatzResearch.WordTrace tailWord_7491679 prefixEnd_7491679 142475268007211092783663 := by
  unfold tailWord_7491679
  simp only [CollatzResearch.WordTrace]
  refine ⟨273243981025933934753950091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182162654017289289835966727 273243981025933934753950091)
  ·
    refine ⟨409865971538900902130925137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273243981025933934753950091 409865971538900902130925137)
    ·
      refine ⟨307399478654175676598193853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409865971538900902130925137 307399478654175676598193853)
      ·
        refine ⟨115274804495315878724322695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307399478654175676598193853 115274804495315878724322695)
        ·
          refine ⟨172912206742973818086484043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115274804495315878724322695 172912206742973818086484043)
          ·
            refine ⟨259368310114460727129726065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172912206742973818086484043 259368310114460727129726065)
            ·
              refine ⟨194526232585845545347294549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259368310114460727129726065 194526232585845545347294549)
              ·
                refine ⟨142475268007211092783663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 194526232585845545347294549 142475268007211092783663)
                ·
                  rfl

theorem cell23_7491679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 12].length) (baseStart_7491679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491679 prefixEnd_7491679 := by exact prefixLift 7491679
  have htrace : WordTrace (prefixWord ++ tailWord_7491679) baseStart_7491679 baseEnd_7491679 := by
    simpa [prefixWord, tailWord_7491679, baseEnd_7491679] using wordTrace_append hprefix tailTrace_7491679
  have hstable : (prefixWord ++ tailWord_7491679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491679).length < 2 ^ (prefixWord ++ tailWord_7491679).sum := by decide
  have hdescent : baseEnd_7491679 < baseStart_7491679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491683 : List Nat := [1, 1, 1, 5, 1, 1, 4, 3, 2, 4]
def baseStart_7491683 : Nat := 118140960795 + 7491683 * 2 ^ 59
def prefixEnd_7491683 : Nat := 4983230072969 + 3 ^ 40 * 7491683 * 2
def baseEnd_7491683 : Nat := 1282278096705772496502961

theorem tailTrace_7491683 : CollatzResearch.WordTrace tailWord_7491683 prefixEnd_7491683 1282278096705772496502961 := by
  unfold tailWord_7491683
  simp only [CollatzResearch.WordTrace]
  refine ⟨273244126917919443437095703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182162751278612962291397135 273244126917919443437095703)
  ·
    refine ⟨409866190376879165155643555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273244126917919443437095703 409866190376879165155643555)
    ·
      refine ⟨614799285565318747733465333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409866190376879165155643555 614799285565318747733465333)
      ·
        refine ⟨57637433021748632600012375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 614799285565318747733465333 57637433021748632600012375)
        ·
          refine ⟨86456149532622948900018563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57637433021748632600012375 86456149532622948900018563)
          ·
            refine ⟨129684224298934423350027845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86456149532622948900018563 129684224298934423350027845)
            ·
              refine ⟨24315792056050204378130221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129684224298934423350027845 24315792056050204378130221)
              ·
                refine ⟨9118422021018826641798833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24315792056050204378130221 9118422021018826641798833)
                ·
                  refine ⟨6838816515764119981349125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9118422021018826641798833 6838816515764119981349125)
                  ·
                    refine ⟨1282278096705772496502961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6838816515764119981349125 1282278096705772496502961)
                    ·
                      rfl

theorem cell23_7491683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 4].length) (baseStart_7491683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491683 prefixEnd_7491683 := by exact prefixLift 7491683
  have htrace : WordTrace (prefixWord ++ tailWord_7491683) baseStart_7491683 baseEnd_7491683 := by
    simpa [prefixWord, tailWord_7491683, baseEnd_7491683] using wordTrace_append hprefix tailTrace_7491683
  have hstable : (prefixWord ++ tailWord_7491683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491683).length < 2 ^ (prefixWord ++ tailWord_7491683).sum := by decide
  have hdescent : baseEnd_7491683 < baseStart_7491683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491693 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_7491693 : Nat := 118140960795 + 7491693 * 2 ^ 59
def prefixEnd_7491693 : Nat := 4983230072969 + 3 ^ 40 * 7491693 * 2
def baseEnd_7491693 : Nat := 3846839424923862450383837

theorem tailTrace_7491693 : CollatzResearch.WordTrace tailWord_7491693 prefixEnd_7491693 3846839424923862450383837 := by
  unfold tailWord_7491693
  simp only [CollatzResearch.WordTrace]
  refine ⟨273244491647883215144959733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182162994431922143429973155 273244491647883215144959733)
  ·
    refine ⟨25616671091989051419839975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273244491647883215144959733 25616671091989051419839975)
    ·
      refine ⟨38425006637983577129759963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25616671091989051419839975 38425006637983577129759963)
      ·
        refine ⟨57637509956975365694639945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38425006637983577129759963 57637509956975365694639945)
        ·
          refine ⟨43228132467731524270979959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57637509956975365694639945 43228132467731524270979959)
          ·
            refine ⟨64842198701597286406469939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43228132467731524270979959 64842198701597286406469939)
            ·
              refine ⟨97263298052395929609704909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64842198701597286406469939 97263298052395929609704909)
              ·
                refine ⟨36473736769648473603639341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97263298052395929609704909 36473736769648473603639341)
                ·
                  refine ⟨13677651288618177601364753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36473736769648473603639341 13677651288618177601364753)
                  ·
                    refine ⟨10258238466463633201023565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13677651288618177601364753 10258238466463633201023565)
                    ·
                      refine ⟨3846839424923862450383837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10258238466463633201023565 3846839424923862450383837)
                      ·
                        rfl

theorem cell23_7491693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_7491693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491693 prefixEnd_7491693 := by exact prefixLift 7491693
  have htrace : WordTrace (prefixWord ++ tailWord_7491693) baseStart_7491693 baseEnd_7491693 := by
    simpa [prefixWord, tailWord_7491693, baseEnd_7491693] using wordTrace_append hprefix tailTrace_7491693
  have hstable : (prefixWord ++ tailWord_7491693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491693).length < 2 ^ (prefixWord ++ tailWord_7491693).sum := by decide
  have hdescent : baseEnd_7491693 < baseStart_7491693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491763 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 3, 4, 2]
def baseStart_7491763 : Nat := 118140960795 + 7491763 * 2 ^ 59
def prefixEnd_7491763 : Nat := 4983230072969 + 3 ^ 40 * 7491763 * 2
def baseEnd_7491763 : Nat := 3846875368569677176508515

theorem tailTrace_7491763 : CollatzResearch.WordTrace tailWord_7491763 prefixEnd_7491763 3846875368569677176508515 := by
  unfold tailWord_7491763
  simp only [CollatzResearch.WordTrace]
  refine ⟨273247044757629617100007943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182164696505086411400005295 273247044757629617100007943)
  ·
    refine ⟨409870567136444425650011915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273247044757629617100007943 409870567136444425650011915)
    ·
      refine ⟨614805850704666638475017873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409870567136444425650011915 614805850704666638475017873)
      ·
        refine ⟨461104388028499978856263405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614805850704666638475017873 461104388028499978856263405)
        ·
          refine ⟨172914145510687492071098777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461104388028499978856263405 172914145510687492071098777)
          ·
            refine ⟨129685609133015619053324083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172914145510687492071098777 129685609133015619053324083)
            ·
              refine ⟨194528413699523428579986125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129685609133015619053324083 194528413699523428579986125)
              ·
                refine ⟨72948155137321285717494797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194528413699523428579986125 72948155137321285717494797)
                ·
                  refine ⟨27355558176495482144060549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72948155137321285717494797 27355558176495482144060549)
                  ·
                    refine ⟨5129167158092902902011353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27355558176495482144060549 5129167158092902902011353)
                    ·
                      refine ⟨3846875368569677176508515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5129167158092902902011353 3846875368569677176508515)
                      ·
                        rfl

theorem cell23_7491763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 4, 2].length) (baseStart_7491763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491763 prefixEnd_7491763 := by exact prefixLift 7491763
  have htrace : WordTrace (prefixWord ++ tailWord_7491763) baseStart_7491763 baseEnd_7491763 := by
    simpa [prefixWord, tailWord_7491763, baseEnd_7491763] using wordTrace_append hprefix tailTrace_7491763
  have hstable : (prefixWord ++ tailWord_7491763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491763).length < 2 ^ (prefixWord ++ tailWord_7491763).sum := by decide
  have hdescent : baseEnd_7491763 < baseStart_7491763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491764 : List Nat := [2, 5, 3, 1, 2, 1, 9]
def baseStart_7491764 : Nat := 118140960795 + 7491764 * 2 ^ 59
def prefixEnd_7491764 : Nat := 4983230072969 + 3 ^ 40 * 7491764 * 2
def baseEnd_7491764 : Nat := 47492294840127551513531

theorem tailTrace_7491764 : CollatzResearch.WordTrace tailWord_7491764 prefixEnd_7491764 47492294840127551513531 := by
  unfold tailWord_7491764
  simp only [CollatzResearch.WordTrace]
  refine ⟨136623540615312997135397173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182164720820417329513862897 136623540615312997135397173)
  ·
    refine ⟨12808456932685593481443485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136623540615312997135397173 12808456932685593481443485)
    ·
      refine ⟨4803171349757097555541307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12808456932685593481443485 4803171349757097555541307)
      ·
        refine ⟨7204757024635646333311961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4803171349757097555541307 7204757024635646333311961)
        ·
          refine ⟨5403567768476734749983971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7204757024635646333311961 5403567768476734749983971)
          ·
            refine ⟨8105351652715102124975957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5403567768476734749983971 8105351652715102124975957)
            ·
              refine ⟨47492294840127551513531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8105351652715102124975957 47492294840127551513531)
              ·
                rfl

theorem cell23_7491764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 9].length) (baseStart_7491764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491764 prefixEnd_7491764 := by exact prefixLift 7491764
  have htrace : WordTrace (prefixWord ++ tailWord_7491764) baseStart_7491764 baseEnd_7491764 := by
    simpa [prefixWord, tailWord_7491764, baseEnd_7491764] using wordTrace_append hprefix tailTrace_7491764
  have hstable : (prefixWord ++ tailWord_7491764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491764).length < 2 ^ (prefixWord ++ tailWord_7491764).sum := by decide
  have hdescent : baseEnd_7491764 < baseStart_7491764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491847 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 2, 3, 3]
def baseStart_7491847 : Nat := 118140960795 + 7491847 * 2 ^ 59
def prefixEnd_7491847 : Nat := 4983230072969 + 3 ^ 40 * 7491847 * 2
def baseEnd_7491847 : Nat := 3846918500944654847858129

theorem tailTrace_7491847 : CollatzResearch.WordTrace tailWord_7491847 prefixEnd_7491847 3846918500944654847858129 := by
  unfold tailWord_7491847
  simp only [CollatzResearch.WordTrace]
  refine ⟨273250108489325299446065795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182166738992883532964043863 273250108489325299446065795)
  ·
    refine ⟨409875162733987949169098693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273250108489325299446065795 409875162733987949169098693)
    ·
      refine ⟨76851593012622740469206005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409875162733987949169098693 76851593012622740469206005)
      ·
        refine ⟨7204836844933381918988063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76851593012622740469206005 7204836844933381918988063)
        ·
          refine ⟨10807255267400072878482095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7204836844933381918988063 10807255267400072878482095)
          ·
            refine ⟨16210882901100109317723143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10807255267400072878482095 16210882901100109317723143)
            ·
              refine ⟨24316324351650163976584715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16210882901100109317723143 24316324351650163976584715)
              ·
                refine ⟨36474486527475245964877073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24316324351650163976584715 36474486527475245964877073)
                ·
                  refine ⟨27355864895606434473657805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36474486527475245964877073 27355864895606434473657805)
                  ·
                    refine ⟨10258449335852412927621677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27355864895606434473657805 10258449335852412927621677)
                    ·
                      refine ⟨3846918500944654847858129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10258449335852412927621677 3846918500944654847858129)
                      ·
                        rfl

theorem cell23_7491847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_7491847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491847 prefixEnd_7491847 := by exact prefixLift 7491847
  have htrace : WordTrace (prefixWord ++ tailWord_7491847) baseStart_7491847 baseEnd_7491847 := by
    simpa [prefixWord, tailWord_7491847, baseEnd_7491847] using wordTrace_append hprefix tailTrace_7491847
  have hstable : (prefixWord ++ tailWord_7491847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491847).length < 2 ^ (prefixWord ++ tailWord_7491847).sum := by decide
  have hdescent : baseEnd_7491847 < baseStart_7491847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491893 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 8]
def baseStart_7491893 : Nat := 118140960795 + 7491893 * 2 ^ 59
def prefixEnd_7491893 : Nat := 4983230072969 + 3 ^ 40 * 7491893 * 2
def baseEnd_7491893 : Nat := 427438013450529074209213

theorem tailTrace_7491893 : CollatzResearch.WordTrace tailWord_7491893 prefixEnd_7491893 427438013450529074209213 := by
  unfold tailWord_7491893
  simp only [CollatzResearch.WordTrace]
  refine ⟨273251786247158649302240333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182167857498105766201493555 273251786247158649302240333)
  ·
    refine ⟨102469419842684493488340125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273251786247158649302240333 102469419842684493488340125)
    ·
      refine ⟨38426032441006685058127547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102469419842684493488340125 38426032441006685058127547)
      ·
        refine ⟨57639048661510027587191321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38426032441006685058127547 57639048661510027587191321)
        ·
          refine ⟨43229286496132520690393491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57639048661510027587191321 43229286496132520690393491)
          ·
            refine ⟨64843929744198781035590237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43229286496132520690393491 64843929744198781035590237)
            ·
              refine ⟨24316473654074542888346339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64843929744198781035590237 24316473654074542888346339)
              ·
                refine ⟨36474710481111814332519509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24316473654074542888346339 36474710481111814332519509)
                ·
                  refine ⟨427438013450529074209213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36474710481111814332519509 427438013450529074209213)
                  ·
                    rfl

theorem cell23_7491893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_7491893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491893 prefixEnd_7491893 := by exact prefixLift 7491893
  have htrace : WordTrace (prefixWord ++ tailWord_7491893) baseStart_7491893 baseEnd_7491893 := by
    simpa [prefixWord, tailWord_7491893, baseEnd_7491893] using wordTrace_append hprefix tailTrace_7491893
  have hstable : (prefixWord ++ tailWord_7491893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491893).length < 2 ^ (prefixWord ++ tailWord_7491893).sum := by decide
  have hdescent : baseEnd_7491893 < baseStart_7491893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491897 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 3, 4]
def baseStart_7491897 : Nat := 118140960795 + 7491897 * 2 ^ 59
def prefixEnd_7491897 : Nat := 4983230072969 + 3 ^ 40 * 7491897 * 2
def baseEnd_7491897 : Nat := 1282314724992459884077633

theorem tailTrace_7491897 : CollatzResearch.WordTrace tailWord_7491897 prefixEnd_7491897 1282314724992459884077633 := by
  unfold tailWord_7491897
  simp only [CollatzResearch.WordTrace]
  refine ⟨273251932139144157985385945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182167954759429438656923963 273251932139144157985385945)
  ·
    refine ⟨204938949104358118489039459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273251932139144157985385945 204938949104358118489039459)
    ·
      refine ⟨307408423656537177733559189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204938949104358118489039459 307408423656537177733559189)
      ·
        refine ⟨14409769858900180206260587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 307408423656537177733559189 14409769858900180206260587)
        ·
          refine ⟨21614654788350270309390881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14409769858900180206260587 21614654788350270309390881)
          ·
            refine ⟨16210991091262702732043161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21614654788350270309390881 16210991091262702732043161)
            ·
              refine ⟨12158243318447027049032371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16210991091262702732043161 12158243318447027049032371)
              ·
                refine ⟨18237364977670540573548557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12158243318447027049032371 18237364977670540573548557)
                ·
                  refine ⟨6839011866626452715080709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18237364977670540573548557 6839011866626452715080709)
                  ·
                    refine ⟨1282314724992459884077633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6839011866626452715080709 1282314724992459884077633)
                    ·
                      rfl

theorem cell23_7491897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 4].length) (baseStart_7491897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491897 prefixEnd_7491897 := by exact prefixLift 7491897
  have htrace : WordTrace (prefixWord ++ tailWord_7491897) baseStart_7491897 baseEnd_7491897 := by
    simpa [prefixWord, tailWord_7491897, baseEnd_7491897] using wordTrace_append hprefix tailTrace_7491897
  have hstable : (prefixWord ++ tailWord_7491897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491897).length < 2 ^ (prefixWord ++ tailWord_7491897).sum := by decide
  have hdescent : baseEnd_7491897 < baseStart_7491897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491940 : List Nat := [2, 3, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_7491940 : Nat := 118140960795 + 7491940 * 2 ^ 59
def prefixEnd_7491940 : Nat := 4983230072969 + 3 ^ 40 * 7491940 * 2
def baseEnd_7491940 : Nat := 1282322084881840994665067

theorem tailTrace_7491940 : CollatzResearch.WordTrace tailWord_7491940 prefixEnd_7491940 1282322084881840994665067 := by
  unfold tailWord_7491940
  simp only [CollatzResearch.WordTrace]
  refine ⟨136626750238994188164600637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182169000318658917552800849 136626750238994188164600637)
  ·
    refine ⟨51235031339622820561725239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136626750238994188164600637 51235031339622820561725239)
    ·
      refine ⟨76852547009434230842587859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51235031339622820561725239 76852547009434230842587859)
      ·
        refine ⟨115278820514151346263881789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76852547009434230842587859 115278820514151346263881789)
        ·
          refine ⟨43229557692806754848955671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115278820514151346263881789 43229557692806754848955671)
          ·
            refine ⟨64844336539210132273433507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43229557692806754848955671 64844336539210132273433507)
            ·
              refine ⟨97266504808815198410150261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64844336539210132273433507 97266504808815198410150261)
              ·
                refine ⟨9118734825826424850951587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97266504808815198410150261 9118734825826424850951587)
                ·
                  refine ⟨13678102238739637276427381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9118734825826424850951587 13678102238739637276427381)
                  ·
                    refine ⟨1282322084881840994665067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13678102238739637276427381 1282322084881840994665067)
                    ·
                      rfl

theorem cell23_7491940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_7491940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491940 prefixEnd_7491940 := by exact prefixLift 7491940
  have htrace : WordTrace (prefixWord ++ tailWord_7491940) baseStart_7491940 baseEnd_7491940 := by
    simpa [prefixWord, tailWord_7491940, baseEnd_7491940] using wordTrace_append hprefix tailTrace_7491940
  have hstable : (prefixWord ++ tailWord_7491940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491940).length < 2 ^ (prefixWord ++ tailWord_7491940).sum := by decide
  have hdescent : baseEnd_7491940 < baseStart_7491940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491954 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 3, 1, 3]
def baseStart_7491954 : Nat := 118140960795 + 7491954 * 2 ^ 59
def prefixEnd_7491954 : Nat := 4983230072969 + 3 ^ 40 * 7491954 * 2
def baseEnd_7491954 : Nat := 3846973443374685929220137

theorem tailTrace_7491954 : CollatzResearch.WordTrace tailWord_7491954 prefixEnd_7491954 3846973443374685929220137 := by
  unfold tailWord_7491954
  simp only [CollatzResearch.WordTrace]
  refine ⟨68313502774984414180052729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182169340733291771146807277 68313502774984414180052729)
  ·
    refine ⟨51235127081238310635039547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68313502774984414180052729 51235127081238310635039547)
    ·
      refine ⟨76852690621857465952559321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51235127081238310635039547 76852690621857465952559321)
      ·
        refine ⟨57639517966393099464419491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76852690621857465952559321 57639517966393099464419491)
        ·
          refine ⟨86459276949589649196629237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57639517966393099464419491 86459276949589649196629237)
          ·
            refine ⟨8105557214024029612183991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86459276949589649196629237 8105557214024029612183991)
            ·
              refine ⟨12158335821036044418275987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8105557214024029612183991 12158335821036044418275987)
              ·
                refine ⟨18237503731554066627413981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12158335821036044418275987 18237503731554066627413981)
                ·
                  refine ⟨6839063899332774985280243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18237503731554066627413981 6839063899332774985280243)
                  ·
                    refine ⟨10258595848999162477920365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6839063899332774985280243 10258595848999162477920365)
                    ·
                      refine ⟨3846973443374685929220137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10258595848999162477920365 3846973443374685929220137)
                      ·
                        rfl

theorem cell23_7491954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_7491954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491954 prefixEnd_7491954 := by exact prefixLift 7491954
  have htrace : WordTrace (prefixWord ++ tailWord_7491954) baseStart_7491954 baseEnd_7491954 := by
    simpa [prefixWord, tailWord_7491954, baseEnd_7491954] using wordTrace_append hprefix tailTrace_7491954
  have hstable : (prefixWord ++ tailWord_7491954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491954).length < 2 ^ (prefixWord ++ tailWord_7491954).sum := by decide
  have hdescent : baseEnd_7491954 < baseStart_7491954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491977 : List Nat := [1, 2, 1, 1, 6, 1, 3, 2, 1, 1, 4]
def baseStart_7491977 : Nat := 118140960795 + 7491977 * 2 ^ 59
def prefixEnd_7491977 : Nat := 4983230072969 + 3 ^ 40 * 7491977 * 2
def baseEnd_7491977 : Nat := 3846985253429739339232531

theorem tailTrace_7491977 : CollatzResearch.WordTrace tailWord_7491977 prefixEnd_7491977 3846985253429739339232531 := by
  unfold tailWord_7491977
  simp only [CollatzResearch.WordTrace]
  refine ⟨273254849978854331648298185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182169899985902887765532123 273254849978854331648298185)
  ·
    refine ⟨204941137484140748736223639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273254849978854331648298185 204941137484140748736223639)
    ·
      refine ⟨307411706226211123104335459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204941137484140748736223639 307411706226211123104335459)
      ·
        refine ⟨461117559339316684656503189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307411706226211123104335459 461117559339316684656503189)
        ·
          refine ⟨21614885594030469593273587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 461117559339316684656503189 21614885594030469593273587)
          ·
            refine ⟨32422328391045704389910381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21614885594030469593273587 32422328391045704389910381)
            ·
              refine ⟨12158373146642139146216393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32422328391045704389910381 12158373146642139146216393)
              ·
                refine ⟨9118779859981604359662295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12158373146642139146216393 9118779859981604359662295)
                ·
                  refine ⟨13678169789972406539493443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9118779859981604359662295 13678169789972406539493443)
                  ·
                    refine ⟨20517254684958609809240165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13678169789972406539493443 20517254684958609809240165)
                    ·
                      refine ⟨3846985253429739339232531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20517254684958609809240165 3846985253429739339232531)
                      ·
                        rfl

theorem cell23_7491977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 1, 4].length) (baseStart_7491977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491977 prefixEnd_7491977 := by exact prefixLift 7491977
  have htrace : WordTrace (prefixWord ++ tailWord_7491977) baseStart_7491977 baseEnd_7491977 := by
    simpa [prefixWord, tailWord_7491977, baseEnd_7491977] using wordTrace_append hprefix tailTrace_7491977
  have hstable : (prefixWord ++ tailWord_7491977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491977).length < 2 ^ (prefixWord ++ tailWord_7491977).sum := by decide
  have hdescent : baseEnd_7491977 < baseStart_7491977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491994 : List Nat := [3, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4]
def baseStart_7491994 : Nat := 118140960795 + 7491994 * 2 ^ 59
def prefixEnd_7491994 : Nat := 4983230072969 + 3 ^ 40 * 7491994 * 2
def baseEnd_7491994 : Nat := 3846993982600865772719953

theorem tailTrace_7491994 : CollatzResearch.WordTrace tailWord_7491994 prefixEnd_7491994 3846993982600865772719953 := by
  unfold tailWord_7491994
  simp only [CollatzResearch.WordTrace]
  refine ⟨68313867504948185887916759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182170313346528495701111357 68313867504948185887916759)
  ·
    refine ⟨102470801257422278831875139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68313867504948185887916759 102470801257422278831875139)
    ·
      refine ⟨153706201886133418247812709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102470801257422278831875139 153706201886133418247812709)
      ·
        refine ⟨28819912853650015921464883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153706201886133418247812709 28819912853650015921464883)
        ·
          refine ⟨43229869280475023882197325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28819912853650015921464883 43229869280475023882197325)
          ·
            refine ⟨16211200980178133955823997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43229869280475023882197325 16211200980178133955823997)
            ·
              refine ⟨6079200367566800233433999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16211200980178133955823997 6079200367566800233433999)
              ·
                refine ⟨9118800551350200350150999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6079200367566800233433999 9118800551350200350150999)
                ·
                  refine ⟨13678200827025300525226499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9118800551350200350150999 13678200827025300525226499)
                  ·
                    refine ⟨20517301240537950787839749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13678200827025300525226499 20517301240537950787839749)
                    ·
                      refine ⟨3846993982600865772719953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20517301240537950787839749 3846993982600865772719953)
                      ·
                        rfl

theorem cell23_7491994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_7491994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7491994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7491994 prefixEnd_7491994 := by exact prefixLift 7491994
  have htrace : WordTrace (prefixWord ++ tailWord_7491994) baseStart_7491994 baseEnd_7491994 := by
    simpa [prefixWord, tailWord_7491994, baseEnd_7491994] using wordTrace_append hprefix tailTrace_7491994
  have hstable : (prefixWord ++ tailWord_7491994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491994).length < 2 ^ (prefixWord ++ tailWord_7491994).sum := by decide
  have hdescent : baseEnd_7491994 < baseStart_7491994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492043 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 3, 8]
def baseStart_7492043 : Nat := 118140960795 + 7492043 * 2 ^ 59
def prefixEnd_7492043 : Nat := 4983230072969 + 3 ^ 40 * 7492043 * 2
def baseEnd_7492043 : Nat := 1282339714384312027002409

theorem tailTrace_7492043 : CollatzResearch.WordTrace tailWord_7492043 prefixEnd_7492043 1282339714384312027002409 := by
  unfold tailWord_7492043
  simp only [CollatzResearch.WordTrace]
  refine ⟨273257257196615224920200783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182171504797743483280133855 273257257196615224920200783)
  ·
    refine ⟨409885885794922837380301175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273257257196615224920200783 409885885794922837380301175)
    ·
      refine ⟨614828828692384256070451763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409885885794922837380301175 614828828692384256070451763)
      ·
        refine ⟨922243243038576384105677645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614828828692384256070451763 922243243038576384105677645)
        ·
          refine ⟨345841216139466144039629117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 922243243038576384105677645 345841216139466144039629117)
          ·
            refine ⟨129690456052299804014860919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345841216139466144039629117 129690456052299804014860919)
            ·
              refine ⟨194535684078449706022291379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129690456052299804014860919 194535684078449706022291379)
              ·
                refine ⟨291803526117674559033437069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194535684078449706022291379 291803526117674559033437069)
                ·
                  refine ⟨109426322294127959637538901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291803526117674559033437069 109426322294127959637538901)
                  ·
                    refine ⟨1282339714384312027002409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109426322294127959637538901 1282339714384312027002409)
                    ·
                      rfl

theorem cell23_7492043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 8].length) (baseStart_7492043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492043 prefixEnd_7492043 := by exact prefixLift 7492043
  have htrace : WordTrace (prefixWord ++ tailWord_7492043) baseStart_7492043 baseEnd_7492043 := by
    simpa [prefixWord, tailWord_7492043, baseEnd_7492043] using wordTrace_append hprefix tailTrace_7492043
  have hstable : (prefixWord ++ tailWord_7492043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492043).length < 2 ^ (prefixWord ++ tailWord_7492043).sum := by decide
  have hdescent : baseEnd_7492043 < baseStart_7492043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492077 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_7492077 : Nat := 118140960795 + 7492077 * 2 ^ 59
def prefixEnd_7492077 : Nat := 4983230072969 + 3 ^ 40 * 7492077 * 2
def baseEnd_7492077 : Nat := 1282345533831729649327357

theorem tailTrace_7492077 : CollatzResearch.WordTrace tailWord_7492077 prefixEnd_7492077 1282345533831729649327357 := by
  unfold tailWord_7492077
  simp only [CollatzResearch.WordTrace]
  refine ⟨273258497278492048726938485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182172331518994699151292323 273258497278492048726938485)
  ·
    refine ⟨25617984119858629568150483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273258497278492048726938485 25617984119858629568150483)
    ·
      refine ⟨38426976179787944352225725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25617984119858629568150483 38426976179787944352225725)
      ·
        refine ⟨14410116067420479132084647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38426976179787944352225725 14410116067420479132084647)
        ·
          refine ⟨21615174101130718698126971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14410116067420479132084647 21615174101130718698126971)
          ·
            refine ⟨32422761151696078047190457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21615174101130718698126971 32422761151696078047190457)
            ·
              refine ⟨24317070863772058535392843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32422761151696078047190457 24317070863772058535392843)
              ·
                refine ⟨36475606295658087803089265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24317070863772058535392843 36475606295658087803089265)
                ·
                  refine ⟨27356704721743565852316949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36475606295658087803089265 27356704721743565852316949)
                  ·
                    refine ⟨1282345533831729649327357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27356704721743565852316949 1282345533831729649327357)
                    ·
                      rfl

theorem cell23_7492077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_7492077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492077 prefixEnd_7492077 := by exact prefixLift 7492077
  have htrace : WordTrace (prefixWord ++ tailWord_7492077) baseStart_7492077 baseEnd_7492077 := by
    simpa [prefixWord, tailWord_7492077, baseEnd_7492077] using wordTrace_append hprefix tailTrace_7492077
  have hstable : (prefixWord ++ tailWord_7492077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492077).length < 2 ^ (prefixWord ++ tailWord_7492077).sum := by decide
  have hdescent : baseEnd_7492077 < baseStart_7492077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492080 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 4]
def baseStart_7492080 : Nat := 118140960795 + 7492080 * 2 ^ 59
def prefixEnd_7492080 : Nat := 4983230072969 + 3 ^ 40 * 7492080 * 2
def baseEnd_7492080 : Nat := 3847038141937152436244557

theorem tailTrace_7492080 : CollatzResearch.WordTrace tailWord_7492080 prefixEnd_7492080 3847038141937152436244557 := by
  unfold tailWord_7492080
  simp only [CollatzResearch.WordTrace]
  refine ⟨136629303348740590119648847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182172404464987453492865129 136629303348740590119648847)
  ·
    refine ⟨204943955023110885179473271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136629303348740590119648847 204943955023110885179473271)
    ·
      refine ⟨307415932534666327769209907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204943955023110885179473271 307415932534666327769209907)
      ·
        refine ⟨461123898801999491653814861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307415932534666327769209907 461123898801999491653814861)
        ·
          refine ⟨172921462050749809370180573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461123898801999491653814861 172921462050749809370180573)
          ·
            refine ⟨64845548269031178513817715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172921462050749809370180573 64845548269031178513817715)
            ·
              refine ⟨97268322403546767770726573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64845548269031178513817715 97268322403546767770726573)
              ·
                refine ⟨36475620901330037914022465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97268322403546767770726573 36475620901330037914022465)
                ·
                  refine ⟨27356715675997528435516849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36475620901330037914022465 27356715675997528435516849)
                  ·
                    refine ⟨20517536756998146326637637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27356715675997528435516849 20517536756998146326637637)
                    ·
                      refine ⟨3847038141937152436244557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20517536756998146326637637 3847038141937152436244557)
                      ·
                        rfl

theorem cell23_7492080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_7492080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492080 prefixEnd_7492080 := by exact prefixLift 7492080
  have htrace : WordTrace (prefixWord ++ tailWord_7492080) baseStart_7492080 baseEnd_7492080 := by
    simpa [prefixWord, tailWord_7492080, baseEnd_7492080] using wordTrace_append hprefix tailTrace_7492080
  have hstable : (prefixWord ++ tailWord_7492080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492080).length < 2 ^ (prefixWord ++ tailWord_7492080).sum := by decide
  have hdescent : baseEnd_7492080 < baseStart_7492080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492127 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 2, 5, 2]
def baseStart_7492127 : Nat := 118140960795 + 7492127 * 2 ^ 59
def prefixEnd_7492127 : Nat := 4983230072969 + 3 ^ 40 * 7492127 * 2
def baseEnd_7492127 : Nat := 3847062275527913752356841

theorem tailTrace_7492127 : CollatzResearch.WordTrace tailWord_7492127 prefixEnd_7492127 3847062275527913752356841 := by
  unfold tailWord_7492127
  simp only [CollatzResearch.WordTrace]
  refine ⟨273260320928310907266258635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182173547285540604844172423 273260320928310907266258635)
  ·
    refine ⟨409890481392466360899387953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273260320928310907266258635 409890481392466360899387953)
    ·
      refine ⟨307417861044349770674540965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409890481392466360899387953 307417861044349770674540965)
      ·
        refine ⟨57640848945815582001476431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307417861044349770674540965 57640848945815582001476431)
        ·
          refine ⟨86461273418723373002214647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57640848945815582001476431 86461273418723373002214647)
          ·
            refine ⟨129691910128085059503321971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86461273418723373002214647 129691910128085059503321971)
            ·
              refine ⟨194537865192127589254982957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129691910128085059503321971 194537865192127589254982957)
              ·
                refine ⟨72951699447047845970618609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194537865192127589254982957 72951699447047845970618609)
                ·
                  refine ⟨54713774585285884477963957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72951699447047845970618609 54713774585285884477963957)
                  ·
                    refine ⟨5129416367370551669809121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54713774585285884477963957 5129416367370551669809121)
                    ·
                      refine ⟨3847062275527913752356841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5129416367370551669809121 3847062275527913752356841)
                      ·
                        rfl

theorem cell23_7492127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_7492127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492127 prefixEnd_7492127 := by exact prefixLift 7492127
  have htrace : WordTrace (prefixWord ++ tailWord_7492127) baseStart_7492127 baseEnd_7492127 := by
    simpa [prefixWord, tailWord_7492127, baseEnd_7492127] using wordTrace_append hprefix tailTrace_7492127
  have hstable : (prefixWord ++ tailWord_7492127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492127).length < 2 ^ (prefixWord ++ tailWord_7492127).sum := by decide
  have hdescent : baseEnd_7492127 < baseStart_7492127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492135 : List Nat := [1, 1, 7, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_7492135 : Nat := 118140960795 + 7492135 * 2 ^ 59
def prefixEnd_7492135 : Nat := 4983230072969 + 3 ^ 40 * 7492135 * 2
def baseEnd_7492135 : Nat := 3847066383373149721056805

theorem tailTrace_7492135 : CollatzResearch.WordTrace tailWord_7492135 prefixEnd_7492135 3847066383373149721056805 := by
  unfold tailWord_7492135
  simp only [CollatzResearch.WordTrace]
  refine ⟨273260612712281924632549859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182173741808187949755033239 273260612712281924632549859)
  ·
    refine ⟨409890919068422886948824789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273260612712281924632549859 409890919068422886948824789)
    ·
      refine ⟨9606818415666161412863081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 409890919068422886948824789 9606818415666161412863081)
      ·
        refine ⟨7205113811749621059647311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9606818415666161412863081 7205113811749621059647311)
        ·
          refine ⟨10807670717624431589470967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7205113811749621059647311 10807670717624431589470967)
          ·
            refine ⟨16211506076436647384206451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10807670717624431589470967 16211506076436647384206451)
            ·
              refine ⟨24317259114654971076309677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16211506076436647384206451 24317259114654971076309677)
              ·
                refine ⟨9118972167995614153616129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24317259114654971076309677 9118972167995614153616129)
                ·
                  refine ⟨6839229125996710615212097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9118972167995614153616129 6839229125996710615212097)
                  ·
                    refine ⟨5129421844497532961409073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6839229125996710615212097 5129421844497532961409073)
                    ·
                      refine ⟨3847066383373149721056805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5129421844497532961409073 3847066383373149721056805)
                      ·
                        rfl

theorem cell23_7492135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_7492135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492135 prefixEnd_7492135 := by exact prefixLift 7492135
  have htrace : WordTrace (prefixWord ++ tailWord_7492135) baseStart_7492135 baseEnd_7492135 := by
    simpa [prefixWord, tailWord_7492135, baseEnd_7492135] using wordTrace_append hprefix tailTrace_7492135
  have hstable : (prefixWord ++ tailWord_7492135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492135).length < 2 ^ (prefixWord ++ tailWord_7492135).sum := by decide
  have hdescent : baseEnd_7492135 < baseStart_7492135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492140 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_7492140 : Nat := 118140960795 + 7492140 * 2 ^ 59
def prefixEnd_7492140 : Nat := 4983230072969 + 3 ^ 40 * 7492140 * 2
def baseEnd_7492140 : Nat := 3847068950776422201494281

theorem tailTrace_7492140 : CollatzResearch.WordTrace tailWord_7492140 prefixEnd_7492140 3847068950776422201494281 := by
  unfold tailWord_7492140
  simp only [CollatzResearch.WordTrace]
  refine ⟨136630397538631905243240937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182173863384842540324321249 136630397538631905243240937)
  ·
    refine ⟨102472798153973928932430703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136630397538631905243240937 102472798153973928932430703)
    ·
      refine ⟨153709197230960893398646055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102472798153973928932430703 153709197230960893398646055)
      ·
        refine ⟨230563795846441340097969083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153709197230960893398646055 230563795846441340097969083)
        ·
          refine ⟨345845693769662010146953625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230563795846441340097969083 345845693769662010146953625)
          ·
            refine ⟨259384270327246507610215219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345845693769662010146953625 259384270327246507610215219)
            ·
              refine ⟨389076405490869761415322829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259384270327246507610215219 389076405490869761415322829)
              ·
                refine ⟨145903652059076160530746061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389076405490869761415322829 145903652059076160530746061)
                ·
                  refine ⟨54713869522153560199029773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145903652059076160530746061 54713869522153560199029773)
                  ·
                    refine ⟨20517701070807585074636165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54713869522153560199029773 20517701070807585074636165)
                    ·
                      refine ⟨3847068950776422201494281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20517701070807585074636165 3847068950776422201494281)
                      ·
                        rfl

theorem cell23_7492140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_7492140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492140 prefixEnd_7492140 := by exact prefixLift 7492140
  have htrace : WordTrace (prefixWord ++ tailWord_7492140) baseStart_7492140 baseEnd_7492140 := by
    simpa [prefixWord, tailWord_7492140, baseEnd_7492140] using wordTrace_append hprefix tailTrace_7492140
  have hstable : (prefixWord ++ tailWord_7492140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492140).length < 2 ^ (prefixWord ++ tailWord_7492140).sum := by decide
  have hdescent : baseEnd_7492140 < baseStart_7492140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492240 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 2, 10]
def baseStart_7492240 : Nat := 118140960795 + 7492240 * 2 ^ 59
def prefixEnd_7492240 : Nat := 4983230072969 + 3 ^ 40 * 7492240 * 2
def baseEnd_7492240 : Nat := 1282373432947290603414607

theorem tailTrace_7492240 : CollatzResearch.WordTrace tailWord_7492240 prefixEnd_7492240 1282373432947290603414607 := by
  unfold tailWord_7492240
  simp only [CollatzResearch.WordTrace]
  refine ⟨136632221188450763782561087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182176294917934351710081449 136632221188450763782561087)
  ·
    refine ⟨204948331782676145673841631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136632221188450763782561087 204948331782676145673841631)
    ·
      refine ⟨307422497674014218510762447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204948331782676145673841631 307422497674014218510762447)
      ·
        refine ⟨461133746511021327766143671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307422497674014218510762447 461133746511021327766143671)
        ·
          refine ⟨691700619766531991649215507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461133746511021327766143671 691700619766531991649215507)
          ·
            refine ⟨1037550929649797987473823261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691700619766531991649215507 1037550929649797987473823261)
            ·
              refine ⟨389081598618674245302683723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1037550929649797987473823261 389081598618674245302683723)
              ·
                refine ⟨583622397928011367954025585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389081598618674245302683723 583622397928011367954025585)
                ·
                  refine ⟨437716798446008525965519189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583622397928011367954025585 437716798446008525965519189)
                  ·
                    refine ⟨1282373432947290603414607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 437716798446008525965519189 1282373432947290603414607)
                    ·
                      rfl

theorem cell23_7492240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_7492240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492240 prefixEnd_7492240 := by exact prefixLift 7492240
  have htrace : WordTrace (prefixWord ++ tailWord_7492240) baseStart_7492240 baseEnd_7492240 := by
    simpa [prefixWord, tailWord_7492240, baseEnd_7492240] using wordTrace_append hprefix tailTrace_7492240
  have hstable : (prefixWord ++ tailWord_7492240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492240).length < 2 ^ (prefixWord ++ tailWord_7492240).sum := by decide
  have hdescent : baseEnd_7492240 < baseStart_7492240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492284 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_7492284 : Nat := 118140960795 + 7492284 * 2 ^ 59
def prefixEnd_7492284 : Nat := 4983230072969 + 3 ^ 40 * 7492284 * 2
def baseEnd_7492284 : Nat := 3847142891990669638093619

theorem tailTrace_7492284 : CollatzResearch.WordTrace tailWord_7492284 prefixEnd_7492284 3847142891990669638093619 := by
  unfold tailWord_7492284
  simp only [CollatzResearch.WordTrace]
  refine ⟨136633023594371061539861953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182177364792494748719815937 136633023594371061539861953)
  ·
    refine ⟨102474767695778296154896465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136633023594371061539861953 102474767695778296154896465)
    ·
      refine ⟨76856075771833722116172349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102474767695778296154896465 76856075771833722116172349)
      ·
        refine ⟨28821028414437645793564631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76856075771833722116172349 28821028414437645793564631)
        ·
          refine ⟨43231542621656468690346947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28821028414437645793564631 43231542621656468690346947)
          ·
            refine ⟨64847313932484703035520421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43231542621656468690346947 64847313932484703035520421)
            ·
              refine ⟨12158871362340881819160079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64847313932484703035520421 12158871362340881819160079)
              ·
                refine ⟨18238307043511322728740119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12158871362340881819160079 18238307043511322728740119)
                ·
                  refine ⟨27357460565266984093110179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18238307043511322728740119 27357460565266984093110179)
                  ·
                    refine ⟨41036190847900476139665269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27357460565266984093110179 41036190847900476139665269)
                    ·
                      refine ⟨3847142891990669638093619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41036190847900476139665269 3847142891990669638093619)
                      ·
                        rfl

theorem cell23_7492284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_7492284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492284 prefixEnd_7492284 := by exact prefixLift 7492284
  have htrace : WordTrace (prefixWord ++ tailWord_7492284) baseStart_7492284 baseEnd_7492284 := by
    simpa [prefixWord, tailWord_7492284, baseEnd_7492284] using wordTrace_append hprefix tailTrace_7492284
  have hstable : (prefixWord ++ tailWord_7492284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492284).length < 2 ^ (prefixWord ++ tailWord_7492284).sum := by decide
  have hdescent : baseEnd_7492284 < baseStart_7492284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492287 : List Nat := [1, 1, 2, 2, 2, 6, 9]
def baseStart_7492287 : Nat := 118140960795 + 7492287 * 2 ^ 59
def prefixEnd_7492287 : Nat := 4983230072969 + 3 ^ 40 * 7492287 * 2
def baseEnd_7492287 : Nat := 47495610276946087979705

theorem tailTrace_7492287 : CollatzResearch.WordTrace tailWord_7492287 prefixEnd_7492287 47495610276946087979705 := by
  unfold tailWord_7492287
  simp only [CollatzResearch.WordTrace]
  refine ⟨273266156607731254592083115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182177437738487503061388743 273266156607731254592083115)
  ·
    refine ⟨409899234911596881888124673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273266156607731254592083115 409899234911596881888124673)
    ·
      refine ⟨307424426183697661416093505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409899234911596881888124673 307424426183697661416093505)
      ·
        refine ⟨230568319637773246062070129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307424426183697661416093505 230568319637773246062070129)
        ·
          refine ⟨172926239728329934546552597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230568319637773246062070129 172926239728329934546552597)
          ·
            refine ⟨8105917487265465681869653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172926239728329934546552597 8105917487265465681869653)
            ·
              refine ⟨47495610276946087979705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8105917487265465681869653 47495610276946087979705)
              ·
                rfl

theorem cell23_7492287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 9].length) (baseStart_7492287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492287 prefixEnd_7492287 := by exact prefixLift 7492287
  have htrace : WordTrace (prefixWord ++ tailWord_7492287) baseStart_7492287 baseEnd_7492287 := by
    simpa [prefixWord, tailWord_7492287, baseEnd_7492287] using wordTrace_append hprefix tailTrace_7492287
  have hstable : (prefixWord ++ tailWord_7492287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492287).length < 2 ^ (prefixWord ++ tailWord_7492287).sum := by decide
  have hdescent : baseEnd_7492287 < baseStart_7492287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492298 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 3, 2, 2]
def baseStart_7492298 : Nat := 118140960795 + 7492298 * 2 ^ 59
def prefixEnd_7492298 : Nat := 4983230072969 + 3 ^ 40 * 7492298 * 2
def baseEnd_7492298 : Nat := 3847150080719832583318555

theorem tailTrace_7492298 : CollatzResearch.WordTrace tailWord_7492298 prefixEnd_7492298 3847150080719832583318555 := by
  unfold tailWord_7492298
  simp only [CollatzResearch.WordTrace]
  refine ⟨68316639452672850867683387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182177705207127602313822365 68316639452672850867683387)
  ·
    refine ⟨102474959179009276301525081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68316639452672850867683387 102474959179009276301525081)
    ·
      refine ⟨76856219384256957226143811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102474959179009276301525081 76856219384256957226143811)
      ·
        refine ⟨115284329076385435839215717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76856219384256957226143811 115284329076385435839215717)
        ·
          refine ⟨21615811701822269219852947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115284329076385435839215717 21615811701822269219852947)
          ·
            refine ⟨32423717552733403829779421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21615811701822269219852947 32423717552733403829779421)
            ·
              refine ⟨12158894082275026436167283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32423717552733403829779421 12158894082275026436167283)
              ·
                refine ⟨18238341123412539654250925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12158894082275026436167283 18238341123412539654250925)
                ·
                  refine ⟨6839377921279702370344097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18238341123412539654250925 6839377921279702370344097)
                  ·
                    refine ⟨5129533440959776777758073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6839377921279702370344097 5129533440959776777758073)
                    ·
                      refine ⟨3847150080719832583318555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5129533440959776777758073 3847150080719832583318555)
                      ·
                        rfl

theorem cell23_7492298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_7492298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492298 prefixEnd_7492298 := by exact prefixLift 7492298
  have htrace : WordTrace (prefixWord ++ tailWord_7492298) baseStart_7492298 baseEnd_7492298 := by
    simpa [prefixWord, tailWord_7492298, baseEnd_7492298] using wordTrace_append hprefix tailTrace_7492298
  have hstable : (prefixWord ++ tailWord_7492298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492298).length < 2 ^ (prefixWord ++ tailWord_7492298).sum := by decide
  have hdescent : baseEnd_7492298 < baseStart_7492298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492308 : List Nat := [2, 4, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_7492308 : Nat := 118140960795 + 7492308 * 2 ^ 59
def prefixEnd_7492308 : Nat := 4983230072969 + 3 ^ 40 * 7492308 * 2
def baseEnd_7492308 : Nat := 1282385071842125848064503

theorem tailTrace_7492308 : CollatzResearch.WordTrace tailWord_7492308 prefixEnd_7492308 1282385071842125848064503 := by
  unfold tailWord_7492308
  simp only [CollatzResearch.WordTrace]
  refine ⟨136633461270327587589298789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182177948360436783452398385 136633461270327587589298789)
  ·
    refine ⟨25618773988186422672993523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136633461270327587589298789 25618773988186422672993523)
    ·
      refine ⟨38428160982279634009490285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25618773988186422672993523 38428160982279634009490285)
      ·
        refine ⟨14410560368354862753558857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38428160982279634009490285 14410560368354862753558857)
        ·
          refine ⟨10807920276266147065169143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14410560368354862753558857 10807920276266147065169143)
          ·
            refine ⟨16211880414399220597753715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10807920276266147065169143 16211880414399220597753715)
            ·
              refine ⟨24317820621598830896630573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16211880414399220597753715 24317820621598830896630573)
              ·
                refine ⟨9119182733099561586236465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24317820621598830896630573 9119182733099561586236465)
                ·
                  refine ⟨6839387049824671189677349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9119182733099561586236465 6839387049824671189677349)
                  ·
                    refine ⟨1282385071842125848064503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6839387049824671189677349 1282385071842125848064503)
                    ·
                      rfl

theorem cell23_7492308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_7492308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492308 prefixEnd_7492308 := by exact prefixLift 7492308
  have htrace : WordTrace (prefixWord ++ tailWord_7492308) baseStart_7492308 baseEnd_7492308 := by
    simpa [prefixWord, tailWord_7492308, baseEnd_7492308] using wordTrace_append hprefix tailTrace_7492308
  have hstable : (prefixWord ++ tailWord_7492308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492308).length < 2 ^ (prefixWord ++ tailWord_7492308).sum := by decide
  have hdescent : baseEnd_7492308 < baseStart_7492308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492314 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3]
def baseStart_7492314 : Nat := 118140960795 + 7492314 * 2 ^ 59
def prefixEnd_7492314 : Nat := 4983230072969 + 3 ^ 40 * 7492314 * 2
def baseEnd_7492314 : Nat := 3847158296410304520718481

theorem tailTrace_7492314 : CollatzResearch.WordTrace tailWord_7492314 prefixEnd_7492314 3847158296410304520718481 := by
  unfold tailWord_7492314
  simp only [CollatzResearch.WordTrace]
  refine ⟨68316785344658359550828999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182178094252422292135543997 68316785344658359550828999)
  ·
    refine ⟨102475178016987539326243499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68316785344658359550828999 102475178016987539326243499)
    ·
      refine ⟨153712767025481308989365249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102475178016987539326243499 153712767025481308989365249)
      ·
        refine ⟨115284575269110981742023937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153712767025481308989365249 115284575269110981742023937)
        ·
          refine ⟨86463431451833236306517953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115284575269110981742023937 86463431451833236306517953)
          ·
            refine ⟨64847573588874927229888465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86463431451833236306517953 64847573588874927229888465)
            ·
              refine ⟨48635680191656195422416349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64847573588874927229888465 48635680191656195422416349)
              ·
                refine ⟨18238380071871073283406131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48635680191656195422416349 18238380071871073283406131)
                ·
                  refine ⟨27357570107806609925109197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18238380071871073283406131 27357570107806609925109197)
                  ·
                    refine ⟨10259088790427478721915949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27357570107806609925109197 10259088790427478721915949)
                    ·
                      refine ⟨3847158296410304520718481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10259088790427478721915949 3847158296410304520718481)
                      ·
                        rfl

theorem cell23_7492314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_7492314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492314 prefixEnd_7492314 := by exact prefixLift 7492314
  have htrace : WordTrace (prefixWord ++ tailWord_7492314) baseStart_7492314 baseEnd_7492314 := by
    simpa [prefixWord, tailWord_7492314, baseEnd_7492314] using wordTrace_append hprefix tailTrace_7492314
  have hstable : (prefixWord ++ tailWord_7492314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492314).length < 2 ^ (prefixWord ++ tailWord_7492314).sum := by decide
  have hdescent : baseEnd_7492314 < baseStart_7492314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492348 : List Nat := [2, 2, 2, 1, 3, 3, 2, 2, 2, 1, 3]
def baseStart_7492348 : Nat := 118140960795 + 7492348 * 2 ^ 59
def prefixEnd_7492348 : Nat := 4983230072969 + 3 ^ 40 * 7492348 * 2
def baseEnd_7492348 : Nat := 3847175754752557387693325

theorem tailTrace_7492348 : CollatzResearch.WordTrace tailWord_7492348 prefixEnd_7492348 3847175754752557387693325 := by
  unfold tailWord_7492348
  simp only [CollatzResearch.WordTrace]
  refine ⟨136634190730255131005026849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182178920973673508006702465 136634190730255131005026849)
  ·
    refine ⟨102475643047691348253770137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136634190730255131005026849 102475643047691348253770137)
    ·
      refine ⟨76856732285768511190327603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102475643047691348253770137 76856732285768511190327603)
      ·
        refine ⟨115285098428652766785491405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76856732285768511190327603 115285098428652766785491405)
        ·
          refine ⟨43231911910744787544559277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115285098428652766785491405 43231911910744787544559277)
          ·
            refine ⟨16211966966529295329209729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43231911910744787544559277 16211966966529295329209729)
            ·
              refine ⟨12158975224896971496907297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16211966966529295329209729 12158975224896971496907297)
              ·
                refine ⟨9119231418672728622680473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12158975224896971496907297 9119231418672728622680473)
                ·
                  refine ⟨6839423564004546467010355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9119231418672728622680473 6839423564004546467010355)
                  ·
                    refine ⟨10259135346006819700515533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6839423564004546467010355 10259135346006819700515533)
                    ·
                      refine ⟨3847175754752557387693325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10259135346006819700515533 3847175754752557387693325)
                      ·
                        rfl

theorem cell23_7492348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_7492348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492348 prefixEnd_7492348 := by exact prefixLift 7492348
  have htrace : WordTrace (prefixWord ++ tailWord_7492348) baseStart_7492348 baseEnd_7492348 := by
    simpa [prefixWord, tailWord_7492348, baseEnd_7492348] using wordTrace_append hprefix tailTrace_7492348
  have hstable : (prefixWord ++ tailWord_7492348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492348).length < 2 ^ (prefixWord ++ tailWord_7492348).sum := by decide
  have hdescent : baseEnd_7492348 < baseStart_7492348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492357 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_7492357 : Nat := 118140960795 + 7492357 * 2 ^ 59
def prefixEnd_7492357 : Nat := 4983230072969 + 3 ^ 40 * 7492357 * 2
def baseEnd_7492357 : Nat := 3847180376078447852480783

theorem tailTrace_7492357 : CollatzResearch.WordTrace tailWord_7492357 prefixEnd_7492357 3847180376078447852480783 := by
  unfold tailWord_7492357
  simp only [CollatzResearch.WordTrace]
  refine ⟨273268709717477656547131325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182179139811651771031420883 273268709717477656547131325)
  ·
    refine ⟨102475766144054121205174247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273268709717477656547131325 102475766144054121205174247)
    ·
      refine ⟨153713649216081181807761371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102475766144054121205174247 153713649216081181807761371)
      ·
        refine ⟨230570473824121772711642057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153713649216081181807761371 230570473824121772711642057)
        ·
          refine ⟨172927855368091329533731543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230570473824121772711642057 172927855368091329533731543)
          ·
            refine ⟨259391783052136994300597315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172927855368091329533731543 259391783052136994300597315)
            ·
              refine ⟨389087674578205491450895973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259391783052136994300597315 389087674578205491450895973)
              ·
                refine ⟨72953938983413529647042995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389087674578205491450895973 72953938983413529647042995)
                ·
                  refine ⟨109430908475120294470564493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72953938983413529647042995 109430908475120294470564493)
                  ·
                    refine ⟨41036590678170110426461685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109430908475120294470564493 41036590678170110426461685)
                    ·
                      refine ⟨3847180376078447852480783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41036590678170110426461685 3847180376078447852480783)
                      ·
                        rfl

theorem cell23_7492357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_7492357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492357 prefixEnd_7492357 := by exact prefixLift 7492357
  have htrace : WordTrace (prefixWord ++ tailWord_7492357) baseStart_7492357 baseEnd_7492357 := by
    simpa [prefixWord, tailWord_7492357, baseEnd_7492357] using wordTrace_append hprefix tailTrace_7492357
  have hstable : (prefixWord ++ tailWord_7492357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492357).length < 2 ^ (prefixWord ++ tailWord_7492357).sum := by decide
  have hdescent : baseEnd_7492357 < baseStart_7492357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492371 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 1, 4, 2]
def baseStart_7492371 : Nat := 118140960795 + 7492371 * 2 ^ 59
def prefixEnd_7492371 : Nat := 4983230072969 + 3 ^ 40 * 7492371 * 2
def baseEnd_7492371 : Nat := 3847187564807610797705719

theorem tailTrace_7492371 : CollatzResearch.WordTrace tailWord_7492371 prefixEnd_7492371 3847187564807610797705719 := by
  unfold tailWord_7492371
  simp only [CollatzResearch.WordTrace]
  refine ⟨273269220339426936938140967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182179480226284624625427311 273269220339426936938140967)
  ·
    refine ⟨409903830509140405407211451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273269220339426936938140967 409903830509140405407211451)
    ·
      refine ⟨614855745763710608110817177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409903830509140405407211451 614855745763710608110817177)
      ·
        refine ⟨461141809322782956083112883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614855745763710608110817177 461141809322782956083112883)
        ·
          refine ⟨691712713984174434124669325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461141809322782956083112883 691712713984174434124669325)
          ·
            refine ⟨259392267744065412796750997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 691712713984174434124669325 259392267744065412796750997)
            ·
              refine ⟨12159012550503066224847703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 259392267744065412796750997 12159012550503066224847703)
              ·
                refine ⟨18238518825754599337271555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12159012550503066224847703 18238518825754599337271555)
                ·
                  refine ⟨27357778238631899005907333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18238518825754599337271555 27357778238631899005907333)
                  ·
                    refine ⟨5129583419743481063607625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27357778238631899005907333 5129583419743481063607625)
                    ·
                      refine ⟨3847187564807610797705719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5129583419743481063607625 3847187564807610797705719)
                      ·
                        rfl

theorem cell23_7492371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 4, 2].length) (baseStart_7492371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492371 prefixEnd_7492371 := by exact prefixLift 7492371
  have htrace : WordTrace (prefixWord ++ tailWord_7492371) baseStart_7492371 baseEnd_7492371 := by
    simpa [prefixWord, tailWord_7492371, baseEnd_7492371] using wordTrace_append hprefix tailTrace_7492371
  have hstable : (prefixWord ++ tailWord_7492371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492371).length < 2 ^ (prefixWord ++ tailWord_7492371).sum := by decide
  have hdescent : baseEnd_7492371 < baseStart_7492371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492387 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 7]
def baseStart_7492387 : Nat := 118140960795 + 7492387 * 2 ^ 59
def prefixEnd_7492387 : Nat := 4983230072969 + 3 ^ 40 * 7492387 * 2
def baseEnd_7492387 : Nat := 3847195780498082735105645

theorem tailTrace_7492387 : CollatzResearch.WordTrace tailWord_7492387 prefixEnd_7492387 3847195780498082735105645 := by
  unfold tailWord_7492387
  simp only [CollatzResearch.WordTrace]
  refine ⟨273269803907368971670723415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182179869271579314447148943 273269803907368971670723415)
  ·
    refine ⟨409904705861053457506085123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273269803907368971670723415 409904705861053457506085123)
    ·
      refine ⟨614857058791580186259127685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409904705861053457506085123 614857058791580186259127685)
      ·
        refine ⟨115285698523421284923586441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 614857058791580186259127685 115285698523421284923586441)
        ·
          refine ⟨86464273892565963692689831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115285698523421284923586441 86464273892565963692689831)
          ·
            refine ⟨129696410838848945539034747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86464273892565963692689831 129696410838848945539034747)
            ·
              refine ⟨194544616258273418308552121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129696410838848945539034747 194544616258273418308552121)
              ·
                refine ⟨145908462193705063731414091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194544616258273418308552121 145908462193705063731414091)
                ·
                  refine ⟨218862693290557595597121137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145908462193705063731414091 218862693290557595597121137)
                  ·
                    refine ⟨164147019967918196697840853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218862693290557595597121137 164147019967918196697840853)
                    ·
                      refine ⟨3847195780498082735105645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164147019967918196697840853 3847195780498082735105645)
                      ·
                        rfl

theorem cell23_7492387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_7492387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492387 prefixEnd_7492387 := by exact prefixLift 7492387
  have htrace : WordTrace (prefixWord ++ tailWord_7492387) baseStart_7492387 baseEnd_7492387 := by
    simpa [prefixWord, tailWord_7492387, baseEnd_7492387] using wordTrace_append hprefix tailTrace_7492387
  have hstable : (prefixWord ++ tailWord_7492387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492387).length < 2 ^ (prefixWord ++ tailWord_7492387).sum := by decide
  have hdescent : baseEnd_7492387 < baseStart_7492387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492405 : List Nat := [1, 3, 3, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_7492405 : Nat := 118140960795 + 7492405 * 2 ^ 59
def prefixEnd_7492405 : Nat := 4983230072969 + 3 ^ 40 * 7492405 * 2
def baseEnd_7492405 : Nat := 3847205023149863664680563

theorem tailTrace_7492405 : CollatzResearch.WordTrace tailWord_7492405 prefixEnd_7492405 3847205023149863664680563 := by
  unfold tailWord_7492405
  simp only [CollatzResearch.WordTrace]
  refine ⟨273270460421303760744878669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182180306947535840496585779 273270460421303760744878669)
  ·
    refine ⟨102476422657988910279329501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273270460421303760744878669 102476422657988910279329501)
    ·
      refine ⟨38428658496745841354748563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102476422657988910279329501 38428658496745841354748563)
      ·
        refine ⟨57642987745118762032122845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38428658496745841354748563 57642987745118762032122845)
        ·
          refine ⟨21616120404419535762046067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57642987745118762032122845 21616120404419535762046067)
          ·
            refine ⟨32424180606629303643069101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21616120404419535762046067 32424180606629303643069101)
            ·
              refine ⟨12159067727485988866150913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32424180606629303643069101 12159067727485988866150913)
              ·
                refine ⟨9119300795614491649613185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12159067727485988866150913 9119300795614491649613185)
                ·
                  refine ⟨6839475596710868737209889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9119300795614491649613185 6839475596710868737209889)
                  ·
                    refine ⟨5129606697533151552907417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6839475596710868737209889 5129606697533151552907417)
                    ·
                      refine ⟨3847205023149863664680563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5129606697533151552907417 3847205023149863664680563)
                      ·
                        rfl

theorem cell23_7492405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_7492405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492405 prefixEnd_7492405 := by exact prefixLift 7492405
  have htrace : WordTrace (prefixWord ++ tailWord_7492405) baseStart_7492405 baseEnd_7492405 := by
    simpa [prefixWord, tailWord_7492405, baseEnd_7492405] using wordTrace_append hprefix tailTrace_7492405
  have hstable : (prefixWord ++ tailWord_7492405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492405).length < 2 ^ (prefixWord ++ tailWord_7492405).sum := by decide
  have hdescent : baseEnd_7492405 < baseStart_7492405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492551 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_7492551 : Nat := 118140960795 + 7492551 * 2 ^ 59
def prefixEnd_7492551 : Nat := 4983230072969 + 3 ^ 40 * 7492551 * 2
def baseEnd_7492551 : Nat := 3847279991325420093454891

theorem tailTrace_7492551 : CollatzResearch.WordTrace tailWord_7492551 prefixEnd_7492551 3847279991325420093454891 := by
  unfold tailWord_7492551
  simp only [CollatzResearch.WordTrace]
  refine ⟨273275785478774827679693507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182183856985849885119795671 273275785478774827679693507)
  ·
    refine ⟨409913678218162241519540261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273275785478774827679693507 409913678218162241519540261)
    ·
      refine ⟨76858814665905420284913799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409913678218162241519540261 76858814665905420284913799)
      ·
        refine ⟨115288221998858130427370699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76858814665905420284913799 115288221998858130427370699)
        ·
          refine ⟨172932332998287195641056049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115288221998858130427370699 172932332998287195641056049)
          ·
            refine ⟨129699249748715396730792037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172932332998287195641056049 129699249748715396730792037)
            ·
              refine ⟨24318609327884136887023507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129699249748715396730792037 24318609327884136887023507)
              ·
                refine ⟨36477913991826205330535261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24318609327884136887023507 36477913991826205330535261)
                ·
                  refine ⟨13679217746934826998950723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36477913991826205330535261 13679217746934826998950723)
                  ·
                    refine ⟨20518826620402240498426085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13679217746934826998950723 20518826620402240498426085)
                    ·
                      refine ⟨3847279991325420093454891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20518826620402240498426085 3847279991325420093454891)
                      ·
                        rfl

theorem cell23_7492551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_7492551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492551 prefixEnd_7492551 := by exact prefixLift 7492551
  have htrace : WordTrace (prefixWord ++ tailWord_7492551) baseStart_7492551 baseEnd_7492551 := by
    simpa [prefixWord, tailWord_7492551, baseEnd_7492551] using wordTrace_append hprefix tailTrace_7492551
  have hstable : (prefixWord ++ tailWord_7492551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492551).length < 2 ^ (prefixWord ++ tailWord_7492551).sum := by decide
  have hdescent : baseEnd_7492551 < baseStart_7492551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492555 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 2, 3, 2]
def baseStart_7492555 : Nat := 118140960795 + 7492555 * 2 ^ 59
def prefixEnd_7492555 : Nat := 4983230072969 + 3 ^ 40 * 7492555 * 2
def baseEnd_7492555 : Nat := 3847282045248038077804873

theorem tailTrace_7492555 : CollatzResearch.WordTrace tailWord_7492555 prefixEnd_7492555 3847282045248038077804873 := by
  unfold tailWord_7492555
  simp only [CollatzResearch.WordTrace]
  refine ⟨273275931370760336362839119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182183954247173557575226079 273275931370760336362839119)
  ·
    refine ⟨409913897056140504544258679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273275931370760336362839119 409913897056140504544258679)
    ·
      refine ⟨614870845584210756816388019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409913897056140504544258679 614870845584210756816388019)
      ·
        refine ⟨922306268376316135224582029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614870845584210756816388019 922306268376316135224582029)
        ·
          refine ⟨345864850641118550709218261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 922306268376316135224582029 345864850641118550709218261)
          ·
            refine ⟨8106207436901216032247303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 345864850641118550709218261 8106207436901216032247303)
            ·
              refine ⟨12159311155351824048370955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8106207436901216032247303 12159311155351824048370955)
              ·
                refine ⟨18238966733027736072556433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12159311155351824048370955 18238966733027736072556433)
                ·
                  refine ⟨13679225049770802054417325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18238966733027736072556433 13679225049770802054417325)
                  ·
                    refine ⟨5129709393664050770406497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13679225049770802054417325 5129709393664050770406497)
                    ·
                      refine ⟨3847282045248038077804873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5129709393664050770406497 3847282045248038077804873)
                      ·
                        rfl

theorem cell23_7492555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 3, 2].length) (baseStart_7492555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492555 prefixEnd_7492555 := by exact prefixLift 7492555
  have htrace : WordTrace (prefixWord ++ tailWord_7492555) baseStart_7492555 baseEnd_7492555 := by
    simpa [prefixWord, tailWord_7492555, baseEnd_7492555] using wordTrace_append hprefix tailTrace_7492555
  have hstable : (prefixWord ++ tailWord_7492555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492555).length < 2 ^ (prefixWord ++ tailWord_7492555).sum := by decide
  have hdescent : baseEnd_7492555 < baseStart_7492555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492561 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 4, 4]
def baseStart_7492561 : Nat := 118140960795 + 7492561 * 2 ^ 59
def prefixEnd_7492561 : Nat := 4983230072969 + 3 ^ 40 * 7492561 * 2
def baseEnd_7492561 : Nat := 1282428375377321684776615

theorem tailTrace_7492561 : CollatzResearch.WordTrace tailWord_7492561 prefixEnd_7492561 1282428375377321684776615 := by
  unfold tailWord_7492561
  simp only [CollatzResearch.WordTrace]
  refine ⟨273276150208738599387557537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182184100139159066258371691 273276150208738599387557537)
  ·
    refine ⟨204957112656553949540668153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273276150208738599387557537 204957112656553949540668153)
    ·
      refine ⟨153717834492415462155501115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204957112656553949540668153 153717834492415462155501115)
      ·
        refine ⟨230576751738623193233251673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153717834492415462155501115 230576751738623193233251673)
        ·
          refine ⟨172932563803967394924938755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230576751738623193233251673 172932563803967394924938755)
          ·
            refine ⟨259398845705951092387408133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172932563803967394924938755 259398845705951092387408133)
            ·
              refine ⟨48637283569865829822639025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259398845705951092387408133 48637283569865829822639025)
              ·
                refine ⟨36477962677399372366979269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48637283569865829822639025 36477962677399372366979269)
                ·
                  refine ⟨6839618002012382318808613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36477962677399372366979269 6839618002012382318808613)
                  ·
                    refine ⟨1282428375377321684776615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6839618002012382318808613 1282428375377321684776615)
                    ·
                      rfl

theorem cell23_7492561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_7492561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492561 prefixEnd_7492561 := by exact prefixLift 7492561
  have htrace : WordTrace (prefixWord ++ tailWord_7492561) baseStart_7492561 baseEnd_7492561 := by
    simpa [prefixWord, tailWord_7492561, baseEnd_7492561] using wordTrace_append hprefix tailTrace_7492561
  have hstable : (prefixWord ++ tailWord_7492561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492561).length < 2 ^ (prefixWord ++ tailWord_7492561).sum := by decide
  have hdescent : baseEnd_7492561 < baseStart_7492561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492562 : List Nat := [3, 2, 2, 3, 1, 1, 1, 5, 1, 1, 3]
def baseStart_7492562 : Nat := 118140960795 + 7492562 * 2 ^ 59
def prefixEnd_7492562 : Nat := 4983230072969 + 3 ^ 40 * 7492562 * 2
def baseEnd_7492562 : Nat := 3847285639612619550417341

theorem tailTrace_7492562 : CollatzResearch.WordTrace tailWord_7492562 prefixEnd_7492562 3847285639612619550417341 := by
  unfold tailWord_7492562
  simp only [CollatzResearch.WordTrace]
  refine ⟨68319046670433744139585985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182184124454489984372229293 68319046670433744139585985)
  ·
    refine ⟨51239285002825308104689489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68319046670433744139585985 51239285002825308104689489)
    ·
      refine ⟨38429463752118981078517117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51239285002825308104689489 38429463752118981078517117)
      ·
        refine ⟨14411048907044617904443919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38429463752118981078517117 14411048907044617904443919)
        ·
          refine ⟨21616573360566926856665879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14411048907044617904443919 21616573360566926856665879)
          ·
            refine ⟨32424860040850390284998819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21616573360566926856665879 32424860040850390284998819)
            ·
              refine ⟨48637290061275585427498229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32424860040850390284998819 48637290061275585427498229)
              ·
                refine ⟨4559745943244586133827959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48637290061275585427498229 4559745943244586133827959)
                ·
                  refine ⟨6839618914866879200741939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4559745943244586133827959 6839618914866879200741939)
                  ·
                    refine ⟨10259428372300318801112909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6839618914866879200741939 10259428372300318801112909)
                    ·
                      refine ⟨3847285639612619550417341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10259428372300318801112909 3847285639612619550417341)
                      ·
                        rfl

theorem cell23_7492562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_7492562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492562 prefixEnd_7492562 := by exact prefixLift 7492562
  have htrace : WordTrace (prefixWord ++ tailWord_7492562) baseStart_7492562 baseEnd_7492562 := by
    simpa [prefixWord, tailWord_7492562, baseEnd_7492562] using wordTrace_append hprefix tailTrace_7492562
  have hstable : (prefixWord ++ tailWord_7492562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492562).length < 2 ^ (prefixWord ++ tailWord_7492562).sum := by decide
  have hdescent : baseEnd_7492562 < baseStart_7492562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492568 : List Nat := [2, 1, 2, 2, 2, 4, 1, 3, 1, 1, 4]
def baseStart_7492568 : Nat := 118140960795 + 7492568 * 2 ^ 59
def prefixEnd_7492568 : Nat := 4983230072969 + 3 ^ 40 * 7492568 * 2
def baseEnd_7492568 : Nat := 3847288720496546526942313

theorem tailTrace_7492568 : CollatzResearch.WordTrace tailWord_7492568 prefixEnd_7492568 3847288720496546526942313 := by
  unfold tailWord_7492568
  simp only [CollatzResearch.WordTrace]
  refine ⟨136638202759856619791531179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182184270346475493055374905 136638202759856619791531179)
  ·
    refine ⟨204957304139784929687296769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136638202759856619791531179 204957304139784929687296769)
    ·
      refine ⟨153717978104838697265472577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204957304139784929687296769 153717978104838697265472577)
      ·
        refine ⟨115288483578629022949104433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153717978104838697265472577 115288483578629022949104433)
        ·
          refine ⟨86466362683971767211828325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115288483578629022949104433 86466362683971767211828325)
          ·
            refine ⟨16212443003244706352217811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86466362683971767211828325 16212443003244706352217811)
            ·
              refine ⟨24318664504867059528326717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16212443003244706352217811 24318664504867059528326717)
              ·
                refine ⟨9119499189325147323122519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24318664504867059528326717 9119499189325147323122519)
                ·
                  refine ⟨13679248783987720984683779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9119499189325147323122519 13679248783987720984683779)
                  ·
                    refine ⟨20518873175981581477025669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13679248783987720984683779 20518873175981581477025669)
                    ·
                      refine ⟨3847288720496546526942313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20518873175981581477025669 3847288720496546526942313)
                      ·
                        rfl

theorem cell23_7492568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_7492568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492568 prefixEnd_7492568 := by exact prefixLift 7492568
  have htrace : WordTrace (prefixWord ++ tailWord_7492568) baseStart_7492568 baseEnd_7492568 := by
    simpa [prefixWord, tailWord_7492568, baseEnd_7492568] using wordTrace_append hprefix tailTrace_7492568
  have hstable : (prefixWord ++ tailWord_7492568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492568).length < 2 ^ (prefixWord ++ tailWord_7492568).sum := by decide
  have hdescent : baseEnd_7492568 < baseStart_7492568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492598 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_7492598 : Nat := 118140960795 + 7492598 * 2 ^ 59
def prefixEnd_7492598 : Nat := 4983230072969 + 3 ^ 40 * 7492598 * 2
def baseEnd_7492598 : Nat := 3847304124916181409567175

theorem tailTrace_7492598 : CollatzResearch.WordTrace tailWord_7492598 prefixEnd_7492598 3847304124916181409567175 := by
  unfold tailWord_7492598
  simp only [CollatzResearch.WordTrace]
  refine ⟨17079843731850284669165903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182184999806403036471102965 17079843731850284669165903)
  ·
    refine ⟨25619765597775427003748855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17079843731850284669165903 25619765597775427003748855)
    ·
      refine ⟨38429648396663140505623283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25619765597775427003748855 38429648396663140505623283)
      ·
        refine ⟨57644472594994710758434925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38429648396663140505623283 57644472594994710758434925)
        ·
          refine ⟨21616677223123016534413097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57644472594994710758434925 21616677223123016534413097)
          ·
            refine ⟨16212507917342262400809823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21616677223123016534413097 16212507917342262400809823)
            ·
              refine ⟨24318761876013393601214735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16212507917342262400809823 24318761876013393601214735)
              ·
                refine ⟨36478142814020090401822103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24318761876013393601214735 36478142814020090401822103)
                ·
                  refine ⟨54717214221030135602733155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36478142814020090401822103 54717214221030135602733155)
                  ·
                    refine ⟨82075821331545203404099733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54717214221030135602733155 82075821331545203404099733)
                    ·
                      refine ⟨3847304124916181409567175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82075821331545203404099733 3847304124916181409567175)
                      ·
                        rfl

theorem cell23_7492598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_7492598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492598 prefixEnd_7492598 := by exact prefixLift 7492598
  have htrace : WordTrace (prefixWord ++ tailWord_7492598) baseStart_7492598 baseEnd_7492598 := by
    simpa [prefixWord, tailWord_7492598, baseEnd_7492598] using wordTrace_append hprefix tailTrace_7492598
  have hstable : (prefixWord ++ tailWord_7492598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492598).length < 2 ^ (prefixWord ++ tailWord_7492598).sum := by decide
  have hdescent : baseEnd_7492598 < baseStart_7492598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492619 : List Nat := [1, 1, 1, 1, 6, 4, 1, 3, 1, 2, 2]
def baseStart_7492619 : Nat := 118140960795 + 7492619 * 2 ^ 59
def prefixEnd_7492619 : Nat := 4983230072969 + 3 ^ 40 * 7492619 * 2
def baseEnd_7492619 : Nat := 3847314908009925827404579

theorem tailTrace_7492619 : CollatzResearch.WordTrace tailWord_7492619 prefixEnd_7492619 3847314908009925827404579 := by
  unfold tailWord_7492619
  simp only [CollatzResearch.WordTrace]
  refine ⟨273278265642528475293168911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182185510428352316862112607 273278265642528475293168911)
  ·
    refine ⟨409917398463792712939753367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273278265642528475293168911 409917398463792712939753367)
    ·
      refine ⟨614876097695689069409630051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409917398463792712939753367 614876097695689069409630051)
      ·
        refine ⟨922314146543533604114445077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614876097695689069409630051 922314146543533604114445077)
        ·
          refine ⟨43233475619228137692864613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 922314146543533604114445077 43233475619228137692864613)
          ·
            refine ⟨8106276678605275817412115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43233475619228137692864613 8106276678605275817412115)
            ·
              refine ⟨12159415017907913726118173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8106276678605275817412115 12159415017907913726118173)
              ·
                refine ⟨4559780631715467647294315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12159415017907913726118173 4559780631715467647294315)
                ·
                  refine ⟨6839670947573201470941473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4559780631715467647294315 6839670947573201470941473)
                  ·
                    refine ⟨5129753210679901103206105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6839670947573201470941473 5129753210679901103206105)
                    ·
                      refine ⟨3847314908009925827404579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5129753210679901103206105 3847314908009925827404579)
                      ·
                        rfl

theorem cell23_7492619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 1, 2, 2].length) (baseStart_7492619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492619 prefixEnd_7492619 := by exact prefixLift 7492619
  have htrace : WordTrace (prefixWord ++ tailWord_7492619) baseStart_7492619 baseEnd_7492619 := by
    simpa [prefixWord, tailWord_7492619, baseEnd_7492619] using wordTrace_append hprefix tailTrace_7492619
  have hstable : (prefixWord ++ tailWord_7492619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492619).length < 2 ^ (prefixWord ++ tailWord_7492619).sum := by decide
  have hdescent : baseEnd_7492619 < baseStart_7492619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492636 : List Nat := [2, 2, 3, 1, 4, 1, 3, 2, 1, 2, 2]
def baseStart_7492636 : Nat := 118140960795 + 7492636 * 2 ^ 59
def prefixEnd_7492636 : Nat := 4983230072969 + 3 ^ 40 * 7492636 * 2
def baseEnd_7492636 : Nat := 3847323637181052260892001

theorem tailTrace_7492636 : CollatzResearch.WordTrace tailWord_7492636 prefixEnd_7492636 3847323637181052260892001 := by
  unfold tailWord_7492636
  simp only [CollatzResearch.WordTrace]
  refine ⟨136639442841733443598268881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182185923788977924797691841 136639442841733443598268881)
  ·
    refine ⟨102479582131300082698701661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136639442841733443598268881 102479582131300082698701661)
    ·
      refine ⟨38429843299237531012013123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102479582131300082698701661 38429843299237531012013123)
      ·
        refine ⟨57644764948856296518019685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38429843299237531012013123 57644764948856296518019685)
        ·
          refine ⟨10808393427910555597128691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57644764948856296518019685 10808393427910555597128691)
          ·
            refine ⟨16212590141865833395693037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10808393427910555597128691 16212590141865833395693037)
            ·
              refine ⟨6079721303199687523384889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16212590141865833395693037 6079721303199687523384889)
              ·
                refine ⟨4559790977399765642538667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6079721303199687523384889 4559790977399765642538667)
                ·
                  refine ⟨6839686466099648463808001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4559790977399765642538667 6839686466099648463808001)
                  ·
                    refine ⟨5129764849574736347856001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6839686466099648463808001 5129764849574736347856001)
                    ·
                      refine ⟨3847323637181052260892001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5129764849574736347856001 3847323637181052260892001)
                      ·
                        rfl

theorem cell23_7492636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_7492636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492636 prefixEnd_7492636 := by exact prefixLift 7492636
  have htrace : WordTrace (prefixWord ++ tailWord_7492636) baseStart_7492636 baseEnd_7492636 := by
    simpa [prefixWord, tailWord_7492636, baseEnd_7492636] using wordTrace_append hprefix tailTrace_7492636
  have hstable : (prefixWord ++ tailWord_7492636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492636).length < 2 ^ (prefixWord ++ tailWord_7492636).sum := by decide
  have hdescent : baseEnd_7492636 < baseStart_7492636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492662 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_7492662 : Nat := 118140960795 + 7492662 * 2 ^ 59
def prefixEnd_7492662 : Nat := 4983230072969 + 3 ^ 40 * 7492662 * 2
def baseEnd_7492662 : Nat := 3847336987678069159166881

theorem tailTrace_7492662 : CollatzResearch.WordTrace tailWord_7492662 prefixEnd_7492662 3847336987678069159166881 := by
  unfold tailWord_7492662
  simp only [CollatzResearch.WordTrace]
  refine ⟨17079989623835793352311515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182186555987581795757989493 17079989623835793352311515)
  ·
    refine ⟨25619984435753690028467273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17079989623835793352311515 25619984435753690028467273)
    ·
      refine ⟨19214988326815267521350455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25619984435753690028467273 19214988326815267521350455)
      ·
        refine ⟨28822482490222901282025683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19214988326815267521350455 28822482490222901282025683)
        ·
          refine ⟨43233723735334351923038525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28822482490222901282025683 43233723735334351923038525)
          ·
            refine ⟨16212646400750381971139447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43233723735334351923038525 16212646400750381971139447)
            ·
              refine ⟨24318969601125572956709171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16212646400750381971139447 24318969601125572956709171)
              ·
                refine ⟨36478454401688359435063757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24318969601125572956709171 36478454401688359435063757)
                ·
                  refine ⟨13679420400633134788148909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36478454401688359435063757 13679420400633134788148909)
                  ·
                    refine ⟨5129782650237425545555841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13679420400633134788148909 5129782650237425545555841)
                    ·
                      refine ⟨3847336987678069159166881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5129782650237425545555841 3847336987678069159166881)
                      ·
                        rfl

theorem cell23_7492662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_7492662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492662 prefixEnd_7492662 := by exact prefixLift 7492662
  have htrace : WordTrace (prefixWord ++ tailWord_7492662) baseStart_7492662 baseEnd_7492662 := by
    simpa [prefixWord, tailWord_7492662, baseEnd_7492662] using wordTrace_append hprefix tailTrace_7492662
  have hstable : (prefixWord ++ tailWord_7492662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492662).length < 2 ^ (prefixWord ++ tailWord_7492662).sum := by decide
  have hdescent : baseEnd_7492662 < baseStart_7492662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492671 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 4]
def baseStart_7492671 : Nat := 118140960795 + 7492671 * 2 ^ 59
def prefixEnd_7492671 : Nat := 4983230072969 + 3 ^ 40 * 7492671 * 2
def baseEnd_7492671 : Nat := 3847341609003959623954339

theorem tailTrace_7492671 : CollatzResearch.WordTrace tailWord_7492671 prefixEnd_7492671 3847341609003959623954339 := by
  unfold tailWord_7492671
  simp only [CollatzResearch.WordTrace]
  refine ⟨273280162238340088174061867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182186774825560058782707911 273280162238340088174061867)
  ·
    refine ⟨409920243357510132261092801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273280162238340088174061867 409920243357510132261092801)
    ·
      refine ⟨307440182518132599195819601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409920243357510132261092801 307440182518132599195819601)
      ·
        refine ⟨230580136888599449396864701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307440182518132599195819601 230580136888599449396864701)
        ·
          refine ⟨86467551333224793523824263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230580136888599449396864701 86467551333224793523824263)
          ·
            refine ⟨129701326999837190285736395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86467551333224793523824263 129701326999837190285736395)
            ·
              refine ⟨194551990499755785428604593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129701326999837190285736395 194551990499755785428604593)
              ·
                refine ⟨145913992874816839071453445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194551990499755785428604593 145913992874816839071453445)
                ·
                  refine ⟨27358873664028157325897521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145913992874816839071453445 27358873664028157325897521)
                  ·
                    refine ⟨20519155248021117994423141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27358873664028157325897521 20519155248021117994423141)
                    ·
                      refine ⟨3847341609003959623954339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20519155248021117994423141 3847341609003959623954339)
                      ·
                        rfl

theorem cell23_7492671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_7492671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492671 prefixEnd_7492671 := by exact prefixLift 7492671
  have htrace : WordTrace (prefixWord ++ tailWord_7492671) baseStart_7492671 baseEnd_7492671 := by
    simpa [prefixWord, tailWord_7492671, baseEnd_7492671] using wordTrace_append hprefix tailTrace_7492671
  have hstable : (prefixWord ++ tailWord_7492671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492671).length < 2 ^ (prefixWord ++ tailWord_7492671).sum := by decide
  have hdescent : baseEnd_7492671 < baseStart_7492671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492692 : List Nat := [2, 4, 1, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_7492692 : Nat := 118140960795 + 7492692 * 2 ^ 59
def prefixEnd_7492692 : Nat := 4983230072969 + 3 ^ 40 * 7492692 * 2
def baseEnd_7492692 : Nat := 3847352392097704041791743

theorem tailTrace_7492692 : CollatzResearch.WordTrace tailWord_7492692 prefixEnd_7492692 3847352392097704041791743 := by
  unfold tailWord_7492692
  simp only [CollatzResearch.WordTrace]
  refine ⟨136640464085632004380288165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182187285447509339173717553 136640464085632004380288165)
  ·
    refine ⟨25620087016056000821304031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136640464085632004380288165 25620087016056000821304031)
    ·
      refine ⟨38430130524084001231956047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25620087016056000821304031 38430130524084001231956047)
      ·
        refine ⟨57645195786126001847934071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38430130524084001231956047 57645195786126001847934071)
        ·
          refine ⟨86467793679189002771901107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57645195786126001847934071 86467793679189002771901107)
          ·
            refine ⟨129701690518783504157851661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86467793679189002771901107 129701690518783504157851661)
            ·
              refine ⟨48638133944543814059194373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129701690518783504157851661 48638133944543814059194373)
              ·
                refine ⟨9119650114601965136098945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48638133944543814059194373 9119650114601965136098945)
                ·
                  refine ⟨6839737585951473852074209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9119650114601965136098945 6839737585951473852074209)
                  ·
                    refine ⟨5129803189463605389055657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6839737585951473852074209 5129803189463605389055657)
                    ·
                      refine ⟨3847352392097704041791743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5129803189463605389055657 3847352392097704041791743)
                      ·
                        rfl

theorem cell23_7492692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_7492692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492692 prefixEnd_7492692 := by exact prefixLift 7492692
  have htrace : WordTrace (prefixWord ++ tailWord_7492692) baseStart_7492692 baseEnd_7492692 := by
    simpa [prefixWord, tailWord_7492692, baseEnd_7492692] using wordTrace_append hprefix tailTrace_7492692
  have hstable : (prefixWord ++ tailWord_7492692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492692).length < 2 ^ (prefixWord ++ tailWord_7492692).sum := by decide
  have hdescent : baseEnd_7492692 < baseStart_7492692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492702 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_7492702 : Nat := 118140960795 + 7492702 * 2 ^ 59
def prefixEnd_7492702 : Nat := 4983230072969 + 3 ^ 40 * 7492702 * 2
def baseEnd_7492702 : Nat := 1282452508968083000888899

theorem tailTrace_7492702 : CollatzResearch.WordTrace tailWord_7492702 prefixEnd_7492702 1282452508968083000888899 := by
  unfold tailWord_7492702
  simp only [CollatzResearch.WordTrace]
  refine ⟨34160161612653472558555045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182187528600818520312293573 34160161612653472558555045)
  ·
    refine ⟨6405030302372526104729071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34160161612653472558555045 6405030302372526104729071)
    ·
      refine ⟨9607545453558789157093607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6405030302372526104729071 9607545453558789157093607)
      ·
        refine ⟨14411318180338183735640411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9607545453558789157093607 14411318180338183735640411)
        ·
          refine ⟨21616977270507275603460617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14411318180338183735640411 21616977270507275603460617)
          ·
            refine ⟨16212732952880456702595463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21616977270507275603460617 16212732952880456702595463)
            ·
              refine ⟨24319099429320685053893195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16212732952880456702595463 24319099429320685053893195)
              ·
                refine ⟨36478649143981027580839793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24319099429320685053893195 36478649143981027580839793)
                ·
                  refine ⟨27358986857985770685629845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36478649143981027580839793 27358986857985770685629845)
                  ·
                    refine ⟨1282452508968083000888899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27358986857985770685629845 1282452508968083000888899)
                    ·
                      rfl

theorem cell23_7492702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_7492702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492702 prefixEnd_7492702 := by exact prefixLift 7492702
  have htrace : WordTrace (prefixWord ++ tailWord_7492702) baseStart_7492702 baseEnd_7492702 := by
    simpa [prefixWord, tailWord_7492702, baseEnd_7492702] using wordTrace_append hprefix tailTrace_7492702
  have hstable : (prefixWord ++ tailWord_7492702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492702).length < 2 ^ (prefixWord ++ tailWord_7492702).sum := by decide
  have hdescent : baseEnd_7492702 < baseStart_7492702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492721 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_7492721 : Nat := 118140960795 + 7492721 * 2 ^ 59
def prefixEnd_7492721 : Nat := 4983230072969 + 3 ^ 40 * 7492721 * 2
def baseEnd_7492721 : Nat := 3847367283036684428329109

theorem tailTrace_7492721 : CollatzResearch.WordTrace tailWord_7492721 prefixEnd_7492721 3847367283036684428329109 := by
  unfold tailWord_7492721
  simp only [CollatzResearch.WordTrace]
  refine ⟨273281985888158946713382017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182187990592105964475588011 273281985888158946713382017)
  ·
    refine ⟨204961489416119210035036513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273281985888158946713382017 204961489416119210035036513)
    ·
      refine ⟨153721117062089407526277385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204961489416119210035036513 153721117062089407526277385)
      ·
        refine ⟨115290837796567055644708039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153721117062089407526277385 115290837796567055644708039)
        ·
          refine ⟨172936256694850583467062059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115290837796567055644708039 172936256694850583467062059)
          ·
            refine ⟨259404385042275875200593089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172936256694850583467062059 259404385042275875200593089)
            ·
              refine ⟨194553288781706906400444817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259404385042275875200593089 194553288781706906400444817)
              ·
                refine ⟨145914966586280179800333613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194553288781706906400444817 145914966586280179800333613)
                ·
                  refine ⟨54718112469855067425125105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145914966586280179800333613 54718112469855067425125105)
                  ·
                    refine ⟨41038584352391300568843829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54718112469855067425125105 41038584352391300568843829)
                    ·
                      refine ⟨3847367283036684428329109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41038584352391300568843829 3847367283036684428329109)
                      ·
                        rfl

theorem cell23_7492721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_7492721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492721 prefixEnd_7492721 := by exact prefixLift 7492721
  have htrace : WordTrace (prefixWord ++ tailWord_7492721) baseStart_7492721 baseEnd_7492721 := by
    simpa [prefixWord, tailWord_7492721, baseEnd_7492721] using wordTrace_append hprefix tailTrace_7492721
  have hstable : (prefixWord ++ tailWord_7492721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492721).length < 2 ^ (prefixWord ++ tailWord_7492721).sum := by decide
  have hdescent : baseEnd_7492721 < baseStart_7492721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492728 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 2, 5]
def baseStart_7492728 : Nat := 118140960795 + 7492728 * 2 ^ 59
def prefixEnd_7492728 : Nat := 4983230072969 + 3 ^ 40 * 7492728 * 2
def baseEnd_7492728 : Nat := 1282456959133755300313859

theorem tailTrace_7492728 : CollatzResearch.WordTrace tailWord_7492728 prefixEnd_7492728 1282456959133755300313859 := by
  unfold tailWord_7492728
  simp only [CollatzResearch.WordTrace]
  refine ⟨136641120599566793454443419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182188160799422391272591225 136641120599566793454443419)
  ·
    refine ⟨204961680899350190181665129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136641120599566793454443419 204961680899350190181665129)
    ·
      refine ⟨153721260674512642636248847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204961680899350190181665129 153721260674512642636248847)
      ·
        refine ⟨230581891011768963954373271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153721260674512642636248847 230581891011768963954373271)
        ·
          refine ⟨345872836517653445931559907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230581891011768963954373271 345872836517653445931559907)
          ·
            refine ⟨518809254776480168897339861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345872836517653445931559907 518809254776480168897339861)
            ·
              refine ⟨12159591908823753958531403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 518809254776480168897339861 12159591908823753958531403)
              ·
                refine ⟨18239387863235630937797105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12159591908823753958531403 18239387863235630937797105)
                ·
                  refine ⟨13679540897426723203347829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18239387863235630937797105 13679540897426723203347829)
                  ·
                    refine ⟨1282456959133755300313859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13679540897426723203347829 1282456959133755300313859)
                    ·
                      rfl

theorem cell23_7492728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_7492728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492728 prefixEnd_7492728 := by exact prefixLift 7492728
  have htrace : WordTrace (prefixWord ++ tailWord_7492728) baseStart_7492728 baseEnd_7492728 := by
    simpa [prefixWord, tailWord_7492728, baseEnd_7492728] using wordTrace_append hprefix tailTrace_7492728
  have hstable : (prefixWord ++ tailWord_7492728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492728).length < 2 ^ (prefixWord ++ tailWord_7492728).sum := by decide
  have hdescent : baseEnd_7492728 < baseStart_7492728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492748 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 2, 1, 4]
def baseStart_7492748 : Nat := 118140960795 + 7492748 * 2 ^ 59
def prefixEnd_7492748 : Nat := 4983230072969 + 3 ^ 40 * 7492748 * 2
def baseEnd_7492748 : Nat := 3847381147014355822691485

theorem tailTrace_7492748 : CollatzResearch.WordTrace tailWord_7492748 prefixEnd_7492748 3847381147014355822691485 := by
  unfold tailWord_7492748
  simp only [CollatzResearch.WordTrace]
  refine ⟨136641485329530565162307449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182188647106040753549743265 136641485329530565162307449)
  ·
    refine ⟨102481113997147923871730587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136641485329530565162307449 102481113997147923871730587)
    ·
      refine ⟨153721670995721885807595881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102481113997147923871730587 153721670995721885807595881)
      ·
        refine ⟨115291253246791414355696911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153721670995721885807595881 115291253246791414355696911)
        ·
          refine ⟨172936879870187121533545367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115291253246791414355696911 172936879870187121533545367)
          ·
            refine ⟨259405319805280682300318051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172936879870187121533545367 259405319805280682300318051)
            ·
              refine ⟨389107979707921023450477077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259405319805280682300318051 389107979707921023450477077)
              ·
                refine ⟨18239436548808797974241113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 389107979707921023450477077 18239436548808797974241113)
                ·
                  refine ⟨13679577411606598480680835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18239436548808797974241113 13679577411606598480680835)
                  ·
                    refine ⟨20519366117409897721021253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13679577411606598480680835 20519366117409897721021253)
                    ·
                      refine ⟨3847381147014355822691485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20519366117409897721021253 3847381147014355822691485)
                      ·
                        rfl

theorem cell23_7492748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_7492748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492748 prefixEnd_7492748 := by exact prefixLift 7492748
  have htrace : WordTrace (prefixWord ++ tailWord_7492748) baseStart_7492748 baseEnd_7492748 := by
    simpa [prefixWord, tailWord_7492748, baseEnd_7492748] using wordTrace_append hprefix tailTrace_7492748
  have hstable : (prefixWord ++ tailWord_7492748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492748).length < 2 ^ (prefixWord ++ tailWord_7492748).sum := by decide
  have hdescent : baseEnd_7492748 < baseStart_7492748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492765 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_7492765 : Nat := 118140960795 + 7492765 * 2 ^ 59
def prefixEnd_7492765 : Nat := 4983230072969 + 3 ^ 40 * 7492765 * 2
def baseEnd_7492765 : Nat := 3847389876185482256178907

theorem tailTrace_7492765 : CollatzResearch.WordTrace tailWord_7492765 prefixEnd_7492765 3847389876185482256178907 := by
  unfold tailWord_7492765
  simp only [CollatzResearch.WordTrace]
  refine ⟨273283590699999542227983749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182189060466666361485322499 273283590699999542227983749)
  ·
    refine ⟨51240673256249914167746953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273283590699999542227983749 51240673256249914167746953)
    ·
      refine ⟨38430504942187435625810215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51240673256249914167746953 38430504942187435625810215)
      ·
        refine ⟨57645757413281153438715323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38430504942187435625810215 57645757413281153438715323)
        ·
          refine ⟨86468636119921730158072985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57645757413281153438715323 86468636119921730158072985)
          ·
            refine ⟨64851477089941297618554739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86468636119921730158072985 64851477089941297618554739)
            ·
              refine ⟨97277215634911946427832109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64851477089941297618554739 97277215634911946427832109)
              ·
                refine ⟨36478955863091979910437041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97277215634911946427832109 36478955863091979910437041)
                ·
                  refine ⟨27359216897318984932827781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36478955863091979910437041 27359216897318984932827781)
                  ·
                    refine ⟨5129853168247309674905209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27359216897318984932827781 5129853168247309674905209)
                    ·
                      refine ⟨3847389876185482256178907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5129853168247309674905209 3847389876185482256178907)
                      ·
                        rfl

theorem cell23_7492765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_7492765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492765 prefixEnd_7492765 := by exact prefixLift 7492765
  have htrace : WordTrace (prefixWord ++ tailWord_7492765) baseStart_7492765 baseEnd_7492765 := by
    simpa [prefixWord, tailWord_7492765, baseEnd_7492765] using wordTrace_append hprefix tailTrace_7492765
  have hstable : (prefixWord ++ tailWord_7492765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492765).length < 2 ^ (prefixWord ++ tailWord_7492765).sum := by decide
  have hdescent : baseEnd_7492765 < baseStart_7492765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492768 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 3]
def baseStart_7492768 : Nat := 118140960795 + 7492768 * 2 ^ 59
def prefixEnd_7492768 : Nat := 4983230072969 + 3 ^ 40 * 7492768 * 2
def baseEnd_7492768 : Nat := 3847391416627445744441393

theorem tailTrace_7492768 : CollatzResearch.WordTrace tailWord_7492768 prefixEnd_7492768 3847391416627445744441393 := by
  unfold tailWord_7492768
  simp only [CollatzResearch.WordTrace]
  refine ⟨136641850059494336870171479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182189133412659115826895305 136641850059494336870171479)
  ·
    refine ⟨204962775089241505305257219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136641850059494336870171479 204962775089241505305257219)
    ·
      refine ⟨307444162633862257957885829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204962775089241505305257219 307444162633862257957885829)
      ·
        refine ⟨57645780493849173367103593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307444162633862257957885829 57645780493849173367103593)
        ·
          refine ⟨43234335370386880025327695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57645780493849173367103593 43234335370386880025327695)
          ·
            refine ⟨64851503055580320037991543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43234335370386880025327695 64851503055580320037991543)
            ·
              refine ⟨97277254583370480056987315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64851503055580320037991543 97277254583370480056987315)
              ·
                refine ⟨145915881875055720085480973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97277254583370480056987315 145915881875055720085480973)
                ·
                  refine ⟨54718455703145895032055365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145915881875055720085480973 54718455703145895032055365)
                  ·
                    refine ⟨10259710444339855318510381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54718455703145895032055365 10259710444339855318510381)
                    ·
                      refine ⟨3847391416627445744441393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10259710444339855318510381 3847391416627445744441393)
                      ·
                        rfl

theorem cell23_7492768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_7492768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492768 prefixEnd_7492768 := by exact prefixLift 7492768
  have htrace : WordTrace (prefixWord ++ tailWord_7492768) baseStart_7492768 baseEnd_7492768 := by
    simpa [prefixWord, tailWord_7492768, baseEnd_7492768] using wordTrace_append hprefix tailTrace_7492768
  have hstable : (prefixWord ++ tailWord_7492768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492768).length < 2 ^ (prefixWord ++ tailWord_7492768).sum := by decide
  have hdescent : baseEnd_7492768 < baseStart_7492768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492785 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 1, 4, 3]
def baseStart_7492785 : Nat := 118140960795 + 7492785 * 2 ^ 59
def prefixEnd_7492785 : Nat := 4983230072969 + 3 ^ 40 * 7492785 * 2
def baseEnd_7492785 : Nat := 3847400145798572177928815

theorem tailTrace_7492785 : CollatzResearch.WordTrace tailWord_7492785 prefixEnd_7492785 3847400145798572177928815 := by
  unfold tailWord_7492785
  simp only [CollatzResearch.WordTrace]
  refine ⟨273284320159927085643711809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182189546773284723762474539 273284320159927085643711809)
  ·
    refine ⟨204963240119945314232783857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273284320159927085643711809 204963240119945314232783857)
    ·
      refine ⟨153722430089958985674587893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204963240119945314232783857 153722430089958985674587893)
      ·
        refine ⟨14411477820933654906992615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153722430089958985674587893 14411477820933654906992615)
        ·
          refine ⟨21617216731400482360488923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14411477820933654906992615 21617216731400482360488923)
          ·
            refine ⟨32425825097100723540733385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21617216731400482360488923 32425825097100723540733385)
            ·
              refine ⟨24319368822825542655550039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32425825097100723540733385 24319368822825542655550039)
              ·
                refine ⟨36479053234238313983325059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24319368822825542655550039 36479053234238313983325059)
                ·
                  refine ⟨54718579851357470974987589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36479053234238313983325059 54718579851357470974987589)
                  ·
                    refine ⟨10259733722129525807810173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54718579851357470974987589 10259733722129525807810173)
                    ·
                      refine ⟨3847400145798572177928815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10259733722129525807810173 3847400145798572177928815)
                      ·
                        rfl

theorem cell23_7492785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_7492785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492785 prefixEnd_7492785 := by exact prefixLift 7492785
  have htrace : WordTrace (prefixWord ++ tailWord_7492785) baseStart_7492785 baseEnd_7492785 := by
    simpa [prefixWord, tailWord_7492785, baseEnd_7492785] using wordTrace_append hprefix tailTrace_7492785
  have hstable : (prefixWord ++ tailWord_7492785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492785).length < 2 ^ (prefixWord ++ tailWord_7492785).sum := by decide
  have hdescent : baseEnd_7492785 < baseStart_7492785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492815 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 3, 1, 3]
def baseStart_7492815 : Nat := 118140960795 + 7492815 * 2 ^ 59
def prefixEnd_7492815 : Nat := 4983230072969 + 3 ^ 40 * 7492815 * 2
def baseEnd_7492815 : Nat := 3847415550218207060553677

theorem tailTrace_7492815 : CollatzResearch.WordTrace tailWord_7492815 prefixEnd_7492815 3847415550218207060553677 := by
  unfold tailWord_7492815
  simp only [CollatzResearch.WordTrace]
  refine ⟨273285414349818400767303899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182190276233212267178202599 273285414349818400767303899)
  ·
    refine ⟨409928121524727601150955849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273285414349818400767303899 409928121524727601150955849)
    ·
      refine ⟨307446091143545700863216887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409928121524727601150955849 307446091143545700863216887)
      ·
        refine ⟨461169136715318551294825331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307446091143545700863216887 461169136715318551294825331)
        ·
          refine ⟨691753705072977826942237997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461169136715318551294825331 691753705072977826942237997)
          ·
            refine ⟨259407639402366685103339249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 691753705072977826942237997 259407639402366685103339249)
            ·
              refine ⟨194555729551775013827504437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259407639402366685103339249 194555729551775013827504437)
              ·
                refine ⟨18239599645478907546328541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194555729551775013827504437 18239599645478907546328541)
                ·
                  refine ⟨6839849867054590329873203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18239599645478907546328541 6839849867054590329873203)
                  ·
                    refine ⟨10259774800581885494809805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6839849867054590329873203 10259774800581885494809805)
                    ·
                      refine ⟨3847415550218207060553677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10259774800581885494809805 3847415550218207060553677)
                      ·
                        rfl

theorem cell23_7492815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 1, 3].length) (baseStart_7492815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492815 prefixEnd_7492815 := by exact prefixLift 7492815
  have htrace : WordTrace (prefixWord ++ tailWord_7492815) baseStart_7492815 baseEnd_7492815 := by
    simpa [prefixWord, tailWord_7492815, baseEnd_7492815] using wordTrace_append hprefix tailTrace_7492815
  have hstable : (prefixWord ++ tailWord_7492815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492815).length < 2 ^ (prefixWord ++ tailWord_7492815).sum := by decide
  have hdescent : baseEnd_7492815 < baseStart_7492815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492825 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 6, 3, 2]
def baseStart_7492825 : Nat := 118140960795 + 7492825 * 2 ^ 59
def prefixEnd_7492825 : Nat := 4983230072969 + 3 ^ 40 * 7492825 * 2
def baseEnd_7492825 : Nat := 3847420685024752021428631

theorem tailTrace_7492825 : CollatzResearch.WordTrace tailWord_7492825 prefixEnd_7492825 3847420685024752021428631 := by
  unfold tailWord_7492825
  simp only [CollatzResearch.WordTrace]
  refine ⟨273285779079782172475167929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182190519386521448316778619 273285779079782172475167929)
  ·
    refine ⟨204964334309836629356375947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273285779079782172475167929 204964334309836629356375947)
    ·
      refine ⟨307446501464754944034563921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204964334309836629356375947 307446501464754944034563921)
      ·
        refine ⟨230584876098566208025922941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307446501464754944034563921 230584876098566208025922941)
        ·
          refine ⟨86469328536962328009721103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230584876098566208025922941 86469328536962328009721103)
          ·
            refine ⟨129703992805443492014581655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86469328536962328009721103 129703992805443492014581655)
            ·
              refine ⟨194555989208165238021872483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129703992805443492014581655 194555989208165238021872483)
              ·
                refine ⟨291833983812247857032808725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194555989208165238021872483 291833983812247857032808725)
                ·
                  refine ⟨13679717991199118298412909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 291833983812247857032808725 13679717991199118298412909)
                  ·
                    refine ⟨5129894246699669361904841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13679717991199118298412909 5129894246699669361904841)
                    ·
                      refine ⟨3847420685024752021428631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5129894246699669361904841 3847420685024752021428631)
                      ·
                        rfl

theorem cell23_7492825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 3, 2].length) (baseStart_7492825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492825 prefixEnd_7492825 := by exact prefixLift 7492825
  have htrace : WordTrace (prefixWord ++ tailWord_7492825) baseStart_7492825 baseEnd_7492825 := by
    simpa [prefixWord, tailWord_7492825, baseEnd_7492825] using wordTrace_append hprefix tailTrace_7492825
  have hstable : (prefixWord ++ tailWord_7492825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492825).length < 2 ^ (prefixWord ++ tailWord_7492825).sum := by decide
  have hdescent : baseEnd_7492825 < baseStart_7492825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492842 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_7492842 : Nat := 118140960795 + 7492842 * 2 ^ 59
def prefixEnd_7492842 : Nat := 4983230072969 + 3 ^ 40 * 7492842 * 2
def baseEnd_7492842 : Nat := 3847429414195878454916053

theorem tailTrace_7492842 : CollatzResearch.WordTrace tailWord_7492842 prefixEnd_7492842 3847429414195878454916053 := by
  unfold tailWord_7492842
  simp only [CollatzResearch.WordTrace]
  refine ⟨68321599780180146094634195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182190932747147056252357853 68321599780180146094634195)
  ·
    refine ⟨102482399670270219141951293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68321599780180146094634195 102482399670270219141951293)
    ·
      refine ⟨38430899876351332178231735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102482399670270219141951293 38430899876351332178231735)
      ·
        refine ⟨57646349814526998267347603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38430899876351332178231735 57646349814526998267347603)
        ·
          refine ⟨86469524721790497401021405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57646349814526998267347603 86469524721790497401021405)
          ·
            refine ⟨32426071770671436525383027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86469524721790497401021405 32426071770671436525383027)
            ·
              refine ⟨48639107656007154788074541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32426071770671436525383027 48639107656007154788074541)
              ·
                refine ⟨18239665371002683045527953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48639107656007154788074541 18239665371002683045527953)
                ·
                  refine ⟨13679749028252012284145965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18239665371002683045527953 13679749028252012284145965)
                  ·
                    refine ⟨5129905885594504606554737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13679749028252012284145965 5129905885594504606554737)
                    ·
                      refine ⟨3847429414195878454916053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5129905885594504606554737 3847429414195878454916053)
                      ·
                        rfl

theorem cell23_7492842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_7492842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492842 prefixEnd_7492842 := by exact prefixLift 7492842
  have htrace : WordTrace (prefixWord ++ tailWord_7492842) baseStart_7492842 baseEnd_7492842 := by
    simpa [prefixWord, tailWord_7492842, baseEnd_7492842] using wordTrace_append hprefix tailTrace_7492842
  have hstable : (prefixWord ++ tailWord_7492842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492842).length < 2 ^ (prefixWord ++ tailWord_7492842).sum := by decide
  have hdescent : baseEnd_7492842 < baseStart_7492842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492875 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 3]
def baseStart_7492875 : Nat := 118140960795 + 7492875 * 2 ^ 59
def prefixEnd_7492875 : Nat := 4983230072969 + 3 ^ 40 * 7492875 * 2
def baseEnd_7492875 : Nat := 3847446359057476825803401

theorem tailTrace_7492875 : CollatzResearch.WordTrace tailWord_7492875 prefixEnd_7492875 3847446359057476825803401 := by
  unfold tailWord_7492875
  simp only [CollatzResearch.WordTrace]
  refine ⟨273287602729601031014488079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182191735153067354009658719 273287602729601031014488079)
  ·
    refine ⟨409931404094401546521732119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273287602729601031014488079 409931404094401546521732119)
    ·
      refine ⟨614897106141602319782598179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409931404094401546521732119 614897106141602319782598179)
      ·
        refine ⟨922345659212403479673897269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614897106141602319782598179 922345659212403479673897269)
        ·
          refine ⟨86469905551162826219427869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 922345659212403479673897269 86469905551162826219427869)
          ·
            refine ⟨32426214581686059832285451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86469905551162826219427869 32426214581686059832285451)
            ·
              refine ⟨48639321872529089748428177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32426214581686059832285451 48639321872529089748428177)
              ·
                refine ⟨36479491404396817311321133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48639321872529089748428177 36479491404396817311321133)
                ·
                  refine ⟨13679809276648806491745425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36479491404396817311321133 13679809276648806491745425)
                  ·
                    refine ⟨10259856957486604868809069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13679809276648806491745425 10259856957486604868809069)
                    ·
                      refine ⟨3847446359057476825803401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10259856957486604868809069 3847446359057476825803401)
                      ·
                        rfl

theorem cell23_7492875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 3].length) (baseStart_7492875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492875 prefixEnd_7492875 := by exact prefixLift 7492875
  have htrace : WordTrace (prefixWord ++ tailWord_7492875) baseStart_7492875 baseEnd_7492875 := by
    simpa [prefixWord, tailWord_7492875, baseEnd_7492875] using wordTrace_append hprefix tailTrace_7492875
  have hstable : (prefixWord ++ tailWord_7492875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492875).length < 2 ^ (prefixWord ++ tailWord_7492875).sum := by decide
  have hdescent : baseEnd_7492875 < baseStart_7492875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492906 : List Nat := [3, 1, 4, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_7492906 : Nat := 118140960795 + 7492906 * 2 ^ 59
def prefixEnd_7492906 : Nat := 4983230072969 + 3 ^ 40 * 7492906 * 2
def baseEnd_7492906 : Nat := 3847462276957766204515759

theorem tailTrace_7492906 : CollatzResearch.WordTrace tailWord_7492906 prefixEnd_7492906 3847462276957766204515759 := by
  unfold tailWord_7492906
  simp only [CollatzResearch.WordTrace]
  refine ⟨68322183348122180827216643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182192488928325815539244381 68322183348122180827216643)
  ·
    refine ⟨102483275022183271240824965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68322183348122180827216643 102483275022183271240824965)
    ·
      refine ⟨19215614066659363357654681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102483275022183271240824965 19215614066659363357654681)
      ·
        refine ⟨14411710549994522518241011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19215614066659363357654681 14411710549994522518241011)
        ·
          refine ⟨21617565824991783777361517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14411710549994522518241011 21617565824991783777361517)
          ·
            refine ⟨8106587184371918916510569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21617565824991783777361517 8106587184371918916510569)
            ·
              refine ⟨6079940388278939187382927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8106587184371918916510569 6079940388278939187382927)
              ·
                refine ⟨9119910582418408781074391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6079940388278939187382927 9119910582418408781074391)
                ·
                  refine ⟨13679865873627613171611587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9119910582418408781074391 13679865873627613171611587)
                  ·
                    refine ⟨20519798810441419757417381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13679865873627613171611587 20519798810441419757417381)
                    ·
                      refine ⟨3847462276957766204515759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20519798810441419757417381 3847462276957766204515759)
                      ·
                        rfl

theorem cell23_7492906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_7492906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492906 prefixEnd_7492906 := by exact prefixLift 7492906
  have htrace : WordTrace (prefixWord ++ tailWord_7492906) baseStart_7492906 baseEnd_7492906 := by
    simpa [prefixWord, tailWord_7492906, baseEnd_7492906] using wordTrace_append hprefix tailTrace_7492906
  have hstable : (prefixWord ++ tailWord_7492906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492906).length < 2 ^ (prefixWord ++ tailWord_7492906).sum := by decide
  have hdescent : baseEnd_7492906 < baseStart_7492906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492922 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3]
def baseStart_7492922 : Nat := 118140960795 + 7492922 * 2 ^ 59
def prefixEnd_7492922 : Nat := 4983230072969 + 3 ^ 40 * 7492922 * 2
def baseEnd_7492922 : Nat := 3847470492648238141915685

theorem tailTrace_7492922 : CollatzResearch.WordTrace tailWord_7492922 prefixEnd_7492922 3847470492648238141915685 := by
  unfold tailWord_7492922
  simp only [CollatzResearch.WordTrace]
  refine ⟨68322329240107689510362255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182192877973620505360966013 68322329240107689510362255)
  ·
    refine ⟨102483493860161534265543383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68322329240107689510362255 102483493860161534265543383)
    ·
      refine ⟨153725240790242301398315075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102483493860161534265543383 153725240790242301398315075)
      ·
        refine ⟨230587861185363452097472613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153725240790242301398315075 230587861185363452097472613)
        ·
          refine ⟨43235223972255647268276115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230587861185363452097472613 43235223972255647268276115)
          ·
            refine ⟨64852835958383470902414173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43235223972255647268276115 64852835958383470902414173)
            ·
              refine ⟨24319813484393801588405315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64852835958383470902414173 24319813484393801588405315)
              ·
                refine ⟨36479720226590702382607973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24319813484393801588405315 36479720226590702382607973)
                ·
                  refine ⟨6839947542485756696738995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36479720226590702382607973 6839947542485756696738995)
                  ·
                    refine ⟨10259921313728635045108493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6839947542485756696738995 10259921313728635045108493)
                    ·
                      refine ⟨3847470492648238141915685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10259921313728635045108493 3847470492648238141915685)
                      ·
                        rfl

theorem cell23_7492922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_7492922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492922 prefixEnd_7492922 := by exact prefixLift 7492922
  have htrace : WordTrace (prefixWord ++ tailWord_7492922) baseStart_7492922 baseEnd_7492922 := by
    simpa [prefixWord, tailWord_7492922, baseEnd_7492922] using wordTrace_append hprefix tailTrace_7492922
  have hstable : (prefixWord ++ tailWord_7492922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492922).length < 2 ^ (prefixWord ++ tailWord_7492922).sum := by decide
  have hdescent : baseEnd_7492922 < baseStart_7492922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492949 : List Nat := [1, 3, 2, 2, 3, 1, 1, 4, 1, 3, 2]
def baseStart_7492949 : Nat := 118140960795 + 7492949 * 2 ^ 59
def prefixEnd_7492949 : Nat := 4983230072969 + 3 ^ 40 * 7492949 * 2
def baseEnd_7492949 : Nat := 3847484356625909536278061

theorem tailTrace_7492949 : CollatzResearch.WordTrace tailWord_7492949 prefixEnd_7492949 3847484356625909536278061 := by
  unfold tailWord_7492949
  simp only [CollatzResearch.WordTrace]
  refine ⟨273290301731332941652681901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182193534487555294435121267 273290301731332941652681901)
  ·
    refine ⟨102483863149249853119755713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273290301731332941652681901 102483863149249853119755713)
    ·
      refine ⟨76862897361937389839816785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102483863149249853119755713 76862897361937389839816785)
      ·
        refine ⟨57647173021453042379862589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76862897361937389839816785 57647173021453042379862589)
        ·
          refine ⟨21617689883044890892448471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57647173021453042379862589 21617689883044890892448471)
          ·
            refine ⟨32426534824567336338672707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21617689883044890892448471 32426534824567336338672707)
            ·
              refine ⟨48639802236851004508009061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32426534824567336338672707 48639802236851004508009061)
              ·
                refine ⟨9119962919409563345251699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48639802236851004508009061 9119962919409563345251699)
                ·
                  refine ⟨13679944379114345017877549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9119962919409563345251699 13679944379114345017877549)
                  ·
                    refine ⟨5129979142167879381704081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13679944379114345017877549 5129979142167879381704081)
                    ·
                      refine ⟨3847484356625909536278061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5129979142167879381704081 3847484356625909536278061)
                      ·
                        rfl

theorem cell23_7492949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_7492949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492949 prefixEnd_7492949 := by exact prefixLift 7492949
  have htrace : WordTrace (prefixWord ++ tailWord_7492949) baseStart_7492949 baseEnd_7492949 := by
    simpa [prefixWord, tailWord_7492949, baseEnd_7492949] using wordTrace_append hprefix tailTrace_7492949
  have hstable : (prefixWord ++ tailWord_7492949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492949).length < 2 ^ (prefixWord ++ tailWord_7492949).sum := by decide
  have hdescent : baseEnd_7492949 < baseStart_7492949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492965 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_7492965 : Nat := 118140960795 + 7492965 * 2 ^ 59
def prefixEnd_7492965 : Nat := 4983230072969 + 3 ^ 40 * 7492965 * 2
def baseEnd_7492965 : Nat := 3847492572316381473677987

theorem tailTrace_7492965 : CollatzResearch.WordTrace tailWord_7492965 prefixEnd_7492965 3847492572316381473677987 := by
  unfold tailWord_7492965
  simp only [CollatzResearch.WordTrace]
  refine ⟨273290885299274976385264349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182193923532849984256842899 273290885299274976385264349)
  ·
    refine ⟨102484081987228116144474131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273290885299274976385264349 102484081987228116144474131)
    ·
      refine ⟨153726122980842174216711197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102484081987228116144474131 153726122980842174216711197)
      ·
        refine ⟨57647296117815815331266699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153726122980842174216711197 57647296117815815331266699)
        ·
          refine ⟨86470944176723722996900049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57647296117815815331266699 86470944176723722996900049)
          ·
            refine ⟨64853208132542792247675037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86470944176723722996900049 64853208132542792247675037)
            ·
              refine ⟨24319953049703547092878139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64853208132542792247675037 24319953049703547092878139)
              ·
                refine ⟨36479929574555320639317209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24319953049703547092878139 36479929574555320639317209)
                ·
                  refine ⟨27359947180916490479487907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36479929574555320639317209 27359947180916490479487907)
                  ·
                    refine ⟨41039920771374735719231861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27359947180916490479487907 41039920771374735719231861)
                    ·
                      refine ⟨3847492572316381473677987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41039920771374735719231861 3847492572316381473677987)
                      ·
                        rfl

theorem cell23_7492965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_7492965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492965 prefixEnd_7492965 := by exact prefixLift 7492965
  have htrace : WordTrace (prefixWord ++ tailWord_7492965) baseStart_7492965 baseEnd_7492965 := by
    simpa [prefixWord, tailWord_7492965, baseEnd_7492965] using wordTrace_append hprefix tailTrace_7492965
  have hstable : (prefixWord ++ tailWord_7492965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492965).length < 2 ^ (prefixWord ++ tailWord_7492965).sum := by decide
  have hdescent : baseEnd_7492965 < baseStart_7492965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492985 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 7]
def baseStart_7492985 : Nat := 118140960795 + 7492985 * 2 ^ 59
def prefixEnd_7492985 : Nat := 4983230072969 + 3 ^ 40 * 7492985 * 2
def baseEnd_7492985 : Nat := 427500315769941266158655

theorem tailTrace_7492985 : CollatzResearch.WordTrace tailWord_7492985 prefixEnd_7492985 427500315769941266158655 := by
  unfold tailWord_7492985
  simp only [CollatzResearch.WordTrace]
  refine ⟨273291614759202519800992409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182194409839468346533994939 273291614759202519800992409)
  ·
    refine ⟨204968711069401889850744307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273291614759202519800992409 204968711069401889850744307)
    ·
      refine ⟨307453066604102834776116461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204968711069401889850744307 307453066604102834776116461)
      ·
        refine ⟨115294899976538563041043673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307453066604102834776116461 115294899976538563041043673)
        ·
          refine ⟨86471174982403922280782755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115294899976538563041043673 86471174982403922280782755)
          ·
            refine ⟨129706762473605883421174133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86471174982403922280782755 129706762473605883421174133)
            ·
              refine ⟨12160008981900551570735075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129706762473605883421174133 12160008981900551570735075)
              ·
                refine ⟨18240013472850827356102613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12160008981900551570735075 18240013472850827356102613)
                ·
                  refine ⟨427500315769941266158655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18240013472850827356102613 427500315769941266158655)
                  ·
                    rfl

theorem cell23_7492985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 7].length) (baseStart_7492985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492985 prefixEnd_7492985 := by exact prefixLift 7492985
  have htrace : WordTrace (prefixWord ++ tailWord_7492985) baseStart_7492985 baseEnd_7492985 := by
    simpa [prefixWord, tailWord_7492985, baseEnd_7492985] using wordTrace_append hprefix tailTrace_7492985
  have hstable : (prefixWord ++ tailWord_7492985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492985).length < 2 ^ (prefixWord ++ tailWord_7492985).sum := by decide
  have hdescent : baseEnd_7492985 < baseStart_7492985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7492996 : List Nat := [2, 3, 2, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_7492996 : Nat := 118140960795 + 7492996 * 2 ^ 59
def prefixEnd_7492996 : Nat := 4983230072969 + 3 ^ 40 * 7492996 * 2
def baseEnd_7492996 : Nat := 3847508490216670852390345

theorem tailTrace_7492996 : CollatzResearch.WordTrace tailWord_7492996 prefixEnd_7492996 3847508490216670852390345 := by
  unfold tailWord_7492996
  simp only [CollatzResearch.WordTrace]
  refine ⟨136646007981081334339821421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182194677308108445786428561 136646007981081334339821421)
  ·
    refine ⟨51242252992905500377433033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136646007981081334339821421 51242252992905500377433033)
    ·
      refine ⟨38431689744679125283074775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51242252992905500377433033 38431689744679125283074775)
      ·
        refine ⟨57647534617018687924612163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38431689744679125283074775 57647534617018687924612163)
        ·
          refine ⟨86471301925528031886918245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57647534617018687924612163 86471301925528031886918245)
          ·
            refine ⟨16213369111036505978797171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86471301925528031886918245 16213369111036505978797171)
            ·
              refine ⟨24320053666554758968195757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16213369111036505978797171 24320053666554758968195757)
              ·
                refine ⟨9120020124958034613073409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24320053666554758968195757 9120020124958034613073409)
                ·
                  refine ⟨6840015093718525959805057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9120020124958034613073409 6840015093718525959805057)
                  ·
                    refine ⟨5130011320288894469853793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6840015093718525959805057 5130011320288894469853793)
                    ·
                      refine ⟨3847508490216670852390345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5130011320288894469853793 3847508490216670852390345)
                      ·
                        rfl

theorem cell23_7492996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_7492996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7492996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7492996 prefixEnd_7492996 := by exact prefixLift 7492996
  have htrace : WordTrace (prefixWord ++ tailWord_7492996) baseStart_7492996 baseEnd_7492996 := by
    simpa [prefixWord, tailWord_7492996, baseEnd_7492996] using wordTrace_append hprefix tailTrace_7492996
  have hstable : (prefixWord ++ tailWord_7492996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7492996).length < 2 ^ (prefixWord ++ tailWord_7492996).sum := by decide
  have hdescent : baseEnd_7492996 < baseStart_7492996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7492996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493035 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 4]
def baseStart_7493035 : Nat := 118140960795 + 7493035 * 2 ^ 59
def prefixEnd_7493035 : Nat := 4983230072969 + 3 ^ 40 * 7493035 * 2
def baseEnd_7493035 : Nat := 3847528515962196199802665

theorem tailTrace_7493035 : CollatzResearch.WordTrace tailWord_7493035 prefixEnd_7493035 3847528515962196199802665 := by
  unfold tailWord_7493035
  simp only [CollatzResearch.WordTrace]
  refine ⟨273293438409021378340312559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182195625606014252226875039 273293438409021378340312559)
  ·
    refine ⟨409940157613532067510468839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273293438409021378340312559 409940157613532067510468839)
    ·
      refine ⟨614910236420298101265703259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409940157613532067510468839 614910236420298101265703259)
      ·
        refine ⟨922365354630447151898554889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614910236420298101265703259 922365354630447151898554889)
        ·
          refine ⟨691774015972835363923916167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922365354630447151898554889 691774015972835363923916167)
          ·
            refine ⟨1037661023959253045885874251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691774015972835363923916167 1037661023959253045885874251)
            ·
              refine ⟨1556491535938879568828811377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037661023959253045885874251 1556491535938879568828811377)
              ·
                refine ⟨1167368651954159676621608533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1556491535938879568828811377 1167368651954159676621608533)
                ·
                  refine ⟨13680101390087808710409475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1167368651954159676621608533 13680101390087808710409475)
                  ·
                    refine ⟨20520152085131713065614213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13680101390087808710409475 20520152085131713065614213)
                    ·
                      refine ⟨3847528515962196199802665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20520152085131713065614213 3847528515962196199802665)
                      ·
                        rfl

theorem cell23_7493035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 4].length) (baseStart_7493035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493035 prefixEnd_7493035 := by exact prefixLift 7493035
  have htrace : WordTrace (prefixWord ++ tailWord_7493035) baseStart_7493035 baseEnd_7493035 := by
    simpa [prefixWord, tailWord_7493035, baseEnd_7493035] using wordTrace_append hprefix tailTrace_7493035
  have hstable : (prefixWord ++ tailWord_7493035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493035).length < 2 ^ (prefixWord ++ tailWord_7493035).sum := by decide
  have hdescent : baseEnd_7493035 < baseStart_7493035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493129 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 2, 3, 2]
def baseStart_7493129 : Nat := 118140960795 + 7493129 * 2 ^ 59
def prefixEnd_7493129 : Nat := 4983230072969 + 3 ^ 40 * 7493129 * 2
def baseEnd_7493129 : Nat := 3847576783143718832027233

theorem tailTrace_7493129 : CollatzResearch.WordTrace tailWord_7493129 prefixEnd_7493129 3847576783143718832027233 := by
  unfold tailWord_7493129
  simp only [CollatzResearch.WordTrace]
  refine ⟨273296866870680832394234441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182197911247120554929489627 273296866870680832394234441)
  ·
    refine ⟨204972650153010624295675831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273296866870680832394234441 204972650153010624295675831)
    ·
      refine ⟨307458975229515936443513747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204972650153010624295675831 307458975229515936443513747)
      ·
        refine ⟨461188462844273904665270621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307458975229515936443513747 461188462844273904665270621)
        ·
          refine ⟨172945673566602714249476483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461188462844273904665270621 172945673566602714249476483)
          ·
            refine ⟨259418510349904071374214725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172945673566602714249476483 259418510349904071374214725)
            ·
              refine ⟨48640970690607013382665261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259418510349904071374214725 48640970690607013382665261)
              ·
                refine ⟨18240364008977630018499473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48640970690607013382665261 18240364008977630018499473)
                ·
                  refine ⟨13680273006733222513874605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18240364008977630018499473 13680273006733222513874605)
                  ·
                    refine ⟨5130102377524958442702977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13680273006733222513874605 5130102377524958442702977)
                    ·
                      refine ⟨3847576783143718832027233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5130102377524958442702977 3847576783143718832027233)
                      ·
                        rfl

theorem cell23_7493129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 3, 2].length) (baseStart_7493129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493129 prefixEnd_7493129 := by exact prefixLift 7493129
  have htrace : WordTrace (prefixWord ++ tailWord_7493129) baseStart_7493129 baseEnd_7493129 := by
    simpa [prefixWord, tailWord_7493129, baseEnd_7493129] using wordTrace_append hprefix tailTrace_7493129
  have hstable : (prefixWord ++ tailWord_7493129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493129).length < 2 ^ (prefixWord ++ tailWord_7493129).sum := by decide
  have hdescent : baseEnd_7493129 < baseStart_7493129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493176 : List Nat := [2, 1, 2, 1, 4, 4, 1, 2, 1, 1, 4]
def baseStart_7493176 : Nat := 118140960795 + 7493176 * 2 ^ 59
def prefixEnd_7493176 : Nat := 4983230072969 + 3 ^ 40 * 7493176 * 2
def baseEnd_7493176 : Nat := 3847600916734480148139517

theorem tailTrace_7493176 : CollatzResearch.WordTrace tailWord_7493176 prefixEnd_7493176 3847600916734480148139517 := by
  unfold tailWord_7493176
  simp only [CollatzResearch.WordTrace]
  refine ⟨136649290550755279710597691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182199054067673706280796921 136649290550755279710597691)
  ·
    refine ⟨204973935826132919565896537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136649290550755279710597691 204973935826132919565896537)
    ·
      refine ⟨153730451869599689674422403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204973935826132919565896537 153730451869599689674422403)
      ·
        refine ⟨230595677804399534511633605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153730451869599689674422403 230595677804399534511633605)
        ·
          refine ⟨43236689588324912720931301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230595677804399534511633605 43236689588324912720931301)
          ·
            refine ⟨8106879297810921135174619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43236689588324912720931301 8106879297810921135174619)
            ·
              refine ⟨12160318946716381702761929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8106879297810921135174619 12160318946716381702761929)
              ·
                refine ⟨9120239210037286277071447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12160318946716381702761929 9120239210037286277071447)
                ·
                  refine ⟨13680358815055929415607171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9120239210037286277071447 13680358815055929415607171)
                  ·
                    refine ⟨20520538222583894123410757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13680358815055929415607171 20520538222583894123410757)
                    ·
                      refine ⟨3847600916734480148139517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20520538222583894123410757 3847600916734480148139517)
                      ·
                        rfl

theorem cell23_7493176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_7493176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493176 prefixEnd_7493176 := by exact prefixLift 7493176
  have htrace : WordTrace (prefixWord ++ tailWord_7493176) baseStart_7493176 baseEnd_7493176 := by
    simpa [prefixWord, tailWord_7493176, baseEnd_7493176] using wordTrace_append hprefix tailTrace_7493176
  have hstable : (prefixWord ++ tailWord_7493176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493176).length < 2 ^ (prefixWord ++ tailWord_7493176).sum := by decide
  have hdescent : baseEnd_7493176 < baseStart_7493176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493190 : List Nat := [6, 1, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_7493190 : Nat := 118140960795 + 7493190 * 2 ^ 59
def prefixEnd_7493190 : Nat := 4983230072969 + 3 ^ 40 * 7493190 * 2
def baseEnd_7493190 : Nat := 1282536035154547697788151

theorem tailTrace_7493190 : CollatzResearch.WordTrace tailWord_7493190 prefixEnd_7493190 1282536035154547697788151 := by
  unfold tailWord_7493190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8540596616358119994131407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182199394482306559874803349 8540596616358119994131407)
  ·
    refine ⟨12810894924537179991197111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8540596616358119994131407 12810894924537179991197111)
    ·
      refine ⟨19216342386805769986795667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12810894924537179991197111 19216342386805769986795667)
      ·
        refine ⟨28824513580208654980193501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19216342386805769986795667 28824513580208654980193501)
        ·
          refine ⟨10809192592578245617572563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28824513580208654980193501 10809192592578245617572563)
          ·
            refine ⟨16213788888867368426358845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10809192592578245617572563 16213788888867368426358845)
            ·
              refine ⟨6080170833325263159884567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16213788888867368426358845 6080170833325263159884567)
              ·
                refine ⟨9120256249987894739826851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6080170833325263159884567 9120256249987894739826851)
                ·
                  refine ⟨13680384374981842109740277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9120256249987894739826851 13680384374981842109740277)
                  ·
                    refine ⟨1282536035154547697788151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13680384374981842109740277 1282536035154547697788151)
                    ·
                      rfl

theorem cell23_7493190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_7493190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493190 prefixEnd_7493190 := by exact prefixLift 7493190
  have htrace : WordTrace (prefixWord ++ tailWord_7493190) baseStart_7493190 baseEnd_7493190 := by
    simpa [prefixWord, tailWord_7493190, baseEnd_7493190] using wordTrace_append hprefix tailTrace_7493190
  have hstable : (prefixWord ++ tailWord_7493190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493190).length < 2 ^ (prefixWord ++ tailWord_7493190).sum := by decide
  have hdescent : baseEnd_7493190 < baseStart_7493190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493209 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 4, 1, 3]
def baseStart_7493209 : Nat := 118140960795 + 7493209 * 2 ^ 59
def prefixEnd_7493209 : Nat := 4983230072969 + 3 ^ 40 * 7493209 * 2
def baseEnd_7493209 : Nat := 3847617861596078519026865

theorem tailTrace_7493209 : CollatzResearch.WordTrace tailWord_7493209 prefixEnd_7493209 3847617861596078519026865 := by
  unfold tailWord_7493209
  simp only [CollatzResearch.WordTrace]
  refine ⟨273299784710391006057146681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182199856473594004038097787 273299784710391006057146681)
  ·
    refine ⟨204974838532793254542860011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273299784710391006057146681 204974838532793254542860011)
    ·
      refine ⟨307462257799189881814290017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204974838532793254542860011 307462257799189881814290017)
      ·
        refine ⟨230596693349392411360717513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307462257799189881814290017 230596693349392411360717513)
        ·
          refine ⟨172947520012044308520538135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230596693349392411360717513 172947520012044308520538135)
          ·
            refine ⟨259421280018066462780807203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172947520012044308520538135 259421280018066462780807203)
            ·
              refine ⟨389131920027099694171210805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259421280018066462780807203 389131920027099694171210805)
              ·
                refine ⟨36481117502540596328551013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 389131920027099694171210805 36481117502540596328551013)
                ·
                  refine ⟨6840209531726361811603315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36481117502540596328551013 6840209531726361811603315)
                  ·
                    refine ⟨10260314297589542717404973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6840209531726361811603315 10260314297589542717404973)
                    ·
                      refine ⟨3847617861596078519026865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10260314297589542717404973 3847617861596078519026865)
                      ·
                        rfl

theorem cell23_7493209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_7493209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493209 prefixEnd_7493209 := by exact prefixLift 7493209
  have htrace : WordTrace (prefixWord ++ tailWord_7493209) baseStart_7493209 baseEnd_7493209 := by
    simpa [prefixWord, tailWord_7493209, baseEnd_7493209] using wordTrace_append hprefix tailTrace_7493209
  have hstable : (prefixWord ++ tailWord_7493209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493209).length < 2 ^ (prefixWord ++ tailWord_7493209).sum := by decide
  have hdescent : baseEnd_7493209 < baseStart_7493209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493226 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_7493226 : Nat := 118140960795 + 7493226 * 2 ^ 59
def prefixEnd_7493226 : Nat := 4983230072969 + 3 ^ 40 * 7493226 * 2
def baseEnd_7493226 : Nat := 3847626590767204952514287

theorem tailTrace_7493226 : CollatzResearch.WordTrace tailWord_7493226 prefixEnd_7493226 3847626590767204952514287 := by
  unfold tailWord_7493226
  simp only [CollatzResearch.WordTrace]
  refine ⟨68325101187832354490128883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182200269834219611973677021 68325101187832354490128883)
  ·
    refine ⟨102487651781748531735193325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68325101187832354490128883 102487651781748531735193325)
    ·
      refine ⟨38432869418155699400697497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102487651781748531735193325 38432869418155699400697497)
      ·
        refine ⟨28824652063616774550523123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38432869418155699400697497 28824652063616774550523123)
        ·
          refine ⟨43236978095425161825784685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28824652063616774550523123 43236978095425161825784685)
          ·
            refine ⟨16213866785784435684669257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43236978095425161825784685 16213866785784435684669257)
            ·
              refine ⟨12160400089338326763501943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16213866785784435684669257 12160400089338326763501943)
              ·
                refine ⟨18240600134007490145252915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12160400089338326763501943 18240600134007490145252915)
                ·
                  refine ⟨27360900201011235217879373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18240600134007490145252915 27360900201011235217879373)
                  ·
                    refine ⟨10260337575379213206704765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27360900201011235217879373 10260337575379213206704765)
                    ·
                      refine ⟨3847626590767204952514287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10260337575379213206704765 3847626590767204952514287)
                      ·
                        rfl

theorem cell23_7493226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_7493226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493226 prefixEnd_7493226 := by exact prefixLift 7493226
  have htrace : WordTrace (prefixWord ++ tailWord_7493226) baseStart_7493226 baseEnd_7493226 := by
    simpa [prefixWord, tailWord_7493226, baseEnd_7493226] using wordTrace_append hprefix tailTrace_7493226
  have hstable : (prefixWord ++ tailWord_7493226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493226).length < 2 ^ (prefixWord ++ tailWord_7493226).sum := by decide
  have hdescent : baseEnd_7493226 < baseStart_7493226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493306 : List Nat := [3, 1, 1, 1, 2, 4, 3, 3, 5]
def baseStart_7493306 : Nat := 118140960795 + 7493306 * 2 ^ 59
def prefixEnd_7493306 : Nat := 4983230072969 + 3 ^ 40 * 7493306 * 2
def baseEnd_7493306 : Nat := 427518629913284959945991

theorem tailTrace_7493306 : CollatzResearch.WordTrace tailWord_7493306 prefixEnd_7493306 427518629913284959945991 := by
  unfold tailWord_7493306
  simp only [CollatzResearch.WordTrace]
  refine ⟨68325830647759897905856943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182202215060693061082285181 68325830647759897905856943)
  ·
    refine ⟨102488745971639846858785415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68325830647759897905856943 102488745971639846858785415)
    ·
      refine ⟨153733118957459770288178123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102488745971639846858785415 153733118957459770288178123)
      ·
        refine ⟨230599678436189655432267185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153733118957459770288178123 230599678436189655432267185)
        ·
          refine ⟨172949758827142241574200389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230599678436189655432267185 172949758827142241574200389)
          ·
            refine ⟨32428079780089170295162573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172949758827142241574200389 32428079780089170295162573)
            ·
              refine ⟨12160529917533438860685965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32428079780089170295162573 12160529917533438860685965)
              ·
                refine ⟨4560198719075039572757237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12160529917533438860685965 4560198719075039572757237)
                ·
                  refine ⟨427518629913284959945991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4560198719075039572757237 427518629913284959945991)
                  ·
                    rfl

theorem cell23_7493306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 5].length) (baseStart_7493306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493306 prefixEnd_7493306 := by exact prefixLift 7493306
  have htrace : WordTrace (prefixWord ++ tailWord_7493306) baseStart_7493306 baseEnd_7493306 := by
    simpa [prefixWord, tailWord_7493306, baseEnd_7493306] using wordTrace_append hprefix tailTrace_7493306
  have hstable : (prefixWord ++ tailWord_7493306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493306).length < 2 ^ (prefixWord ++ tailWord_7493306).sum := by decide
  have hdescent : baseEnd_7493306 < baseStart_7493306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493319 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 2, 5]
def baseStart_7493319 : Nat := 118140960795 + 7493319 * 2 ^ 59
def prefixEnd_7493319 : Nat := 4983230072969 + 3 ^ 40 * 7493319 * 2
def baseEnd_7493319 : Nat := 1282558114822691029550453

theorem tailTrace_7493319 : CollatzResearch.WordTrace tailWord_7493319 prefixEnd_7493319 1282558114822691029550453 := by
  unfold tailWord_7493319
  simp only [CollatzResearch.WordTrace]
  refine ⟨273303796739992494843651011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182202531159994996562434007 273303796739992494843651011)
  ·
    refine ⟨409955695109988742265476517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273303796739992494843651011 409955695109988742265476517)
    ·
      refine ⟨76866692833122889174776847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409955695109988742265476517 76866692833122889174776847)
      ·
        refine ⟨115300039249684333762165271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76866692833122889174776847 115300039249684333762165271)
        ·
          refine ⟨172950058874526500643247907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115300039249684333762165271 172950058874526500643247907)
          ·
            refine ⟨259425088311789750964871861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172950058874526500643247907 259425088311789750964871861)
            ·
              refine ⟨24321102029230289152956737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259425088311789750964871861 24321102029230289152956737)
              ·
                refine ⟨18240826521922716864717553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24321102029230289152956737 18240826521922716864717553)
                ·
                  refine ⟨13680619891442037648538165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18240826521922716864717553 13680619891442037648538165)
                  ·
                    refine ⟨1282558114822691029550453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13680619891442037648538165 1282558114822691029550453)
                    ·
                      rfl

theorem cell23_7493319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_7493319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493319 prefixEnd_7493319 := by exact prefixLift 7493319
  have htrace : WordTrace (prefixWord ++ tailWord_7493319) baseStart_7493319 baseEnd_7493319 := by
    simpa [prefixWord, tailWord_7493319, baseEnd_7493319] using wordTrace_append hprefix tailTrace_7493319
  have hstable : (prefixWord ++ tailWord_7493319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493319).length < 2 ^ (prefixWord ++ tailWord_7493319).sum := by decide
  have hdescent : baseEnd_7493319 < baseStart_7493319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493326 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2]
def baseStart_7493326 : Nat := 118140960795 + 7493326 * 2 ^ 59
def prefixEnd_7493326 : Nat := 4983230072969 + 3 ^ 40 * 7493326 * 2
def baseEnd_7493326 : Nat := 3847677938832654561263827

theorem tailTrace_7493326 : CollatzResearch.WordTrace tailWord_7493326 prefixEnd_7493326 3847677938832654561263827 := by
  unfold tailWord_7493326
  simp only [CollatzResearch.WordTrace]
  refine ⟨34163006506370891879894479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182202701367311423359437221 34163006506370891879894479)
  ·
    refine ⟨51244509759556337819841719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34163006506370891879894479 51244509759556337819841719)
    ·
      refine ⟨76866764639334506729762579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51244509759556337819841719 76866764639334506729762579)
      ·
        refine ⟨115300146959001760094643869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76866764639334506729762579 115300146959001760094643869)
        ·
          refine ⟨43237555109625660035491451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115300146959001760094643869 43237555109625660035491451)
          ·
            refine ⟨64856332664438490053237177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43237555109625660035491451 64856332664438490053237177)
            ·
              refine ⟨48642249498328867539927883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64856332664438490053237177 48642249498328867539927883)
              ·
                refine ⟨72963374247493301309891825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48642249498328867539927883 72963374247493301309891825)
                ·
                  refine ⟨54722530685619975982418869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72963374247493301309891825 54722530685619975982418869)
                  ·
                    refine ⟨5130237251776872748351769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54722530685619975982418869 5130237251776872748351769)
                    ·
                      refine ⟨3847677938832654561263827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5130237251776872748351769 3847677938832654561263827)
                      ·
                        rfl

theorem cell23_7493326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_7493326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493326 prefixEnd_7493326 := by exact prefixLift 7493326
  have htrace : WordTrace (prefixWord ++ tailWord_7493326) baseStart_7493326 baseEnd_7493326 := by
    simpa [prefixWord, tailWord_7493326, baseEnd_7493326] using wordTrace_append hprefix tailTrace_7493326
  have hstable : (prefixWord ++ tailWord_7493326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493326).length < 2 ^ (prefixWord ++ tailWord_7493326).sum := by decide
  have hdescent : baseEnd_7493326 < baseStart_7493326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493329 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 1, 2, 5]
def baseStart_7493329 : Nat := 118140960795 + 7493329 * 2 ^ 59
def prefixEnd_7493329 : Nat := 4983230072969 + 3 ^ 40 * 7493329 * 2
def baseEnd_7493329 : Nat := 3847679479274618049526313

theorem tailTrace_7493329 : CollatzResearch.WordTrace tailWord_7493329 prefixEnd_7493329 3847679479274618049526313 := by
  unfold tailWord_7493329
  simp only [CollatzResearch.WordTrace]
  refine ⟨273304161469956266551515041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182202774313304177701010027 273304161469956266551515041)
  ·
    refine ⟨204978121102467199913636281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273304161469956266551515041 204978121102467199913636281)
    ·
      refine ⟨153733590826850399935227211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204978121102467199913636281 153733590826850399935227211)
      ·
        refine ⟨230600386240275599902840817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153733590826850399935227211 230600386240275599902840817)
        ·
          refine ⟨172950289680206699927130613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230600386240275599902840817 172950289680206699927130613)
          ·
            refine ⟨16214089657519378118168495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172950289680206699927130613 16214089657519378118168495)
            ·
              refine ⟨24321134486279067177252743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16214089657519378118168495 24321134486279067177252743)
              ·
                refine ⟨36481701729418600765879115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24321134486279067177252743 36481701729418600765879115)
                ·
                  refine ⟨54722552594127901148818673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36481701729418600765879115 54722552594127901148818673)
                  ·
                    refine ⟨41041914445595925861614005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54722552594127901148818673 41041914445595925861614005)
                    ·
                      refine ⟨3847679479274618049526313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41041914445595925861614005 3847679479274618049526313)
                      ·
                        rfl

theorem cell23_7493329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_7493329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493329 prefixEnd_7493329 := by exact prefixLift 7493329
  have htrace : WordTrace (prefixWord ++ tailWord_7493329) baseStart_7493329 baseEnd_7493329 := by
    simpa [prefixWord, tailWord_7493329, baseEnd_7493329] using wordTrace_append hprefix tailTrace_7493329
  have hstable : (prefixWord ++ tailWord_7493329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493329).length < 2 ^ (prefixWord ++ tailWord_7493329).sum := by decide
  have hdescent : baseEnd_7493329 < baseStart_7493329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493334 : List Nat := [5, 2, 1, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_7493334 : Nat := 118140960795 + 7493334 * 2 ^ 59
def prefixEnd_7493334 : Nat := 4983230072969 + 3 ^ 40 * 7493334 * 2
def baseEnd_7493334 : Nat := 3847682046677890529963791

theorem tailTrace_7493334 : CollatzResearch.WordTrace tailWord_7493334 prefixEnd_7493334 3847682046677890529963791 := by
  unfold tailWord_7493334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17081521489683634525340441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182202895889958768270298037 17081521489683634525340441)
  ·
    refine ⟨12811141117262725894005331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17081521489683634525340441 12811141117262725894005331)
    ·
      refine ⟨19216711675894088841007997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12811141117262725894005331 19216711675894088841007997)
      ·
        refine ⟨7206266878460283315377999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19216711675894088841007997 7206266878460283315377999)
        ·
          refine ⟨10809400317690424973066999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7206266878460283315377999 10809400317690424973066999)
          ·
            refine ⟨16214100476535637459600499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10809400317690424973066999 16214100476535637459600499)
            ·
              refine ⟨24321150714803456189400749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16214100476535637459600499 24321150714803456189400749)
              ·
                refine ⟨9120431518051296071025281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24321150714803456189400749 9120431518051296071025281)
                ·
                  refine ⟨6840323638538472053268961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9120431518051296071025281 6840323638538472053268961)
                  ·
                    refine ⟨5130242728903854039951721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6840323638538472053268961 5130242728903854039951721)
                    ·
                      refine ⟨3847682046677890529963791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5130242728903854039951721 3847682046677890529963791)
                      ·
                        rfl

theorem cell23_7493334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_7493334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493334 prefixEnd_7493334 := by exact prefixLift 7493334
  have htrace : WordTrace (prefixWord ++ tailWord_7493334) baseStart_7493334 baseEnd_7493334 := by
    simpa [prefixWord, tailWord_7493334, baseEnd_7493334] using wordTrace_append hprefix tailTrace_7493334
  have hstable : (prefixWord ++ tailWord_7493334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493334).length < 2 ^ (prefixWord ++ tailWord_7493334).sum := by decide
  have hdescent : baseEnd_7493334 < baseStart_7493334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493379 : List Nat := [1, 1, 1, 3, 2, 2, 3, 4, 6]
def baseStart_7493379 : Nat := 118140960795 + 7493379 * 2 ^ 59
def prefixEnd_7493379 : Nat := 4983230072969 + 3 ^ 40 * 7493379 * 2
def baseEnd_7493379 : Nat := 427522794811926983766787

theorem tailTrace_7493379 : CollatzResearch.WordTrace tailWord_7493379 prefixEnd_7493379 427522794811926983766787 := by
  unfold tailWord_7493379
  simp only [CollatzResearch.WordTrace]
  refine ⟨273305985119775125090835191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182203990079850083393890127 273305985119775125090835191)
  ·
    refine ⟨409958977679662687636252787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273305985119775125090835191 409958977679662687636252787)
    ·
      refine ⟨614938466519494031454379181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409958977679662687636252787 614938466519494031454379181)
      ·
        refine ⟨230601924944810261795392193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 614938466519494031454379181 230601924944810261795392193)
        ·
          refine ⟨172951443708607696346544145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230601924944810261795392193 172951443708607696346544145)
          ·
            refine ⟨129713582781455772259908109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172951443708607696346544145 129713582781455772259908109)
            ·
              refine ⟨48642593543045914597465541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129713582781455772259908109 48642593543045914597465541)
              ·
                refine ⟨9120486289321108987024789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48642593543045914597465541 9120486289321108987024789)
                ·
                  refine ⟨427522794811926983766787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9120486289321108987024789 427522794811926983766787)
                  ·
                    rfl

theorem cell23_7493379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 6].length) (baseStart_7493379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493379 prefixEnd_7493379 := by exact prefixLift 7493379
  have htrace : WordTrace (prefixWord ++ tailWord_7493379) baseStart_7493379 baseEnd_7493379 := by
    simpa [prefixWord, tailWord_7493379, baseEnd_7493379] using wordTrace_append hprefix tailTrace_7493379
  have hstable : (prefixWord ++ tailWord_7493379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493379).length < 2 ^ (prefixWord ++ tailWord_7493379).sum := by decide
  have hdescent : baseEnd_7493379 < baseStart_7493379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493430 : List Nat := [5, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_7493430 : Nat := 118140960795 + 7493430 * 2 ^ 59
def prefixEnd_7493430 : Nat := 4983230072969 + 3 ^ 40 * 7493430 * 2
def baseEnd_7493430 : Nat := 427525704535635794929261

theorem tailTrace_7493430 : CollatzResearch.WordTrace tailWord_7493430 prefixEnd_7493430 427525704535635794929261 := by
  unfold tailWord_7493430
  simp only [CollatzResearch.WordTrace]
  refine ⟨17081740327661897550058859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182205230161726907200627829 17081740327661897550058859)
  ·
    refine ⟨25622610491492846325088289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17081740327661897550058859 25622610491492846325088289)
    ·
      refine ⟨19216957868619634743816217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25622610491492846325088289 19216957868619634743816217)
      ·
        refine ⟨14412718401464726057862163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19216957868619634743816217 14412718401464726057862163)
        ·
          refine ⟨21619077602197089086793245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14412718401464726057862163 21619077602197089086793245)
          ·
            refine ⟨8107154100823908407547467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21619077602197089086793245 8107154100823908407547467)
            ·
              refine ⟨12160731151235862611321201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8107154100823908407547467 12160731151235862611321201)
              ·
                refine ⟨9120548363426896958490901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12160731151235862611321201 9120548363426896958490901)
                ·
                  refine ⟨427525704535635794929261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9120548363426896958490901 427525704535635794929261)
                  ·
                    rfl

theorem cell23_7493430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_7493430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493430 prefixEnd_7493430 := by exact prefixLift 7493430
  have htrace : WordTrace (prefixWord ++ tailWord_7493430) baseStart_7493430 baseEnd_7493430 := by
    simpa [prefixWord, tailWord_7493430, baseEnd_7493430] using wordTrace_append hprefix tailTrace_7493430
  have hstable : (prefixWord ++ tailWord_7493430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493430).length < 2 ^ (prefixWord ++ tailWord_7493430).sum := by decide
  have hdescent : baseEnd_7493430 < baseStart_7493430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493474 : List Nat := [3, 3, 2, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_7493474 : Nat := 118140960795 + 7493474 * 2 ^ 59
def prefixEnd_7493474 : Nat := 4983230072969 + 3 ^ 40 * 7493474 * 2
def baseEnd_7493474 : Nat := 3847753933969519982213147

theorem tailTrace_7493474 : CollatzResearch.WordTrace tailWord_7493474 prefixEnd_7493474 3847753933969519982213147 := by
  unfold tailWord_7493474
  simp only [CollatzResearch.WordTrace]
  refine ⟨68327362513607739078885869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182206300036287304210362317 68327362513607739078885869)
  ·
    refine ⟨25622760942602902154582201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68327362513607739078885869 25622760942602902154582201)
    ·
      refine ⟨19217070706952176615936651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25622760942602902154582201 19217070706952176615936651)
      ·
        refine ⟨28825606060428264923904977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19217070706952176615936651 28825606060428264923904977)
        ·
          refine ⟨21619204545321198692928733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28825606060428264923904977 21619204545321198692928733)
          ·
            refine ⟨8107201704495449509848275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21619204545321198692928733 8107201704495449509848275)
            ·
              refine ⟨12160802556743174264772413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8107201704495449509848275 12160802556743174264772413)
              ·
                refine ⟨4560300958778690349289655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12160802556743174264772413 4560300958778690349289655)
                ·
                  refine ⟨6840451438168035523934483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4560300958778690349289655 6840451438168035523934483)
                  ·
                    refine ⟨10260677157252053285901725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6840451438168035523934483 10260677157252053285901725)
                    ·
                      refine ⟨3847753933969519982213147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10260677157252053285901725 3847753933969519982213147)
                      ·
                        rfl

theorem cell23_7493474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_7493474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493474 prefixEnd_7493474 := by exact prefixLift 7493474
  have htrace : WordTrace (prefixWord ++ tailWord_7493474) baseStart_7493474 baseEnd_7493474 := by
    simpa [prefixWord, tailWord_7493474, baseEnd_7493474] using wordTrace_append hprefix tailTrace_7493474
  have hstable : (prefixWord ++ tailWord_7493474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493474).length < 2 ^ (prefixWord ++ tailWord_7493474).sum := by decide
  have hdescent : baseEnd_7493474 < baseStart_7493474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493486 : List Nat := [4, 1, 2, 3, 1, 1, 11]
def baseStart_7493486 : Nat := 118140960795 + 7493486 * 2 ^ 59
def prefixEnd_7493486 : Nat := 4983230072969 + 3 ^ 40 * 7493486 * 2
def baseEnd_7493486 : Nat := 47503211058486097966211

theorem tailTrace_7493486 : CollatzResearch.WordTrace tailWord_7493486 prefixEnd_7493486 47503211058486097966211 := by
  unfold tailWord_7493486
  simp only [CollatzResearch.WordTrace]
  refine ⟨34163735966298435295622539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182206591820258321576653541 34163735966298435295622539)
  ·
    refine ⟨51245603949447652943433809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34163735966298435295622539 51245603949447652943433809)
    ·
      refine ⟨38434202962085739707575357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51245603949447652943433809 38434202962085739707575357)
      ·
        refine ⟨14412826110782152390340759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38434202962085739707575357 14412826110782152390340759)
        ·
          refine ⟨21619239166173228585511139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14412826110782152390340759 21619239166173228585511139)
          ·
            refine ⟨32428858749259842878266709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21619239166173228585511139 32428858749259842878266709)
            ·
              refine ⟨47503211058486097966211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32428858749259842878266709 47503211058486097966211)
              ·
                rfl

theorem cell23_7493486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 11].length) (baseStart_7493486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493486 prefixEnd_7493486 := by exact prefixLift 7493486
  have htrace : WordTrace (prefixWord ++ tailWord_7493486) baseStart_7493486 baseEnd_7493486 := by
    simpa [prefixWord, tailWord_7493486, baseEnd_7493486] using wordTrace_append hprefix tailTrace_7493486
  have hstable : (prefixWord ++ tailWord_7493486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493486).length < 2 ^ (prefixWord ++ tailWord_7493486).sum := by decide
  have hdescent : baseEnd_7493486 < baseStart_7493486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493499 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 2, 7]
def baseStart_7493499 : Nat := 118140960795 + 7493499 * 2 ^ 59
def prefixEnd_7493499 : Nat := 4983230072969 + 3 ^ 40 * 7493499 * 2
def baseEnd_7493499 : Nat := 1282588923661960794800177

theorem tailTrace_7493499 : CollatzResearch.WordTrace tailWord_7493499 prefixEnd_7493499 1282588923661960794800177 := by
  unfold tailWord_7493499
  simp only [CollatzResearch.WordTrace]
  refine ⟨273310361879340385585203551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182206907919560257056802367 273310361879340385585203551)
  ·
    refine ⟨409965542819010578377805327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273310361879340385585203551 409965542819010578377805327)
    ·
      refine ⟨614948314228515867566707991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409965542819010578377805327 614948314228515867566707991)
      ·
        refine ⟨922422471342773801350061987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614948314228515867566707991 922422471342773801350061987)
        ·
          refine ⟨1383633707014160702025092981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 922422471342773801350061987 1383633707014160702025092981)
          ·
            refine ⟨129715660032577565814852467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1383633707014160702025092981 129715660032577565814852467)
            ·
              refine ⟨194573490048866348722278701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129715660032577565814852467 194573490048866348722278701)
              ·
                refine ⟨72965058768324880770854513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194573490048866348722278701 72965058768324880770854513)
                ·
                  refine ⟨54723794076243660578140885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72965058768324880770854513 54723794076243660578140885)
                  ·
                    refine ⟨1282588923661960794800177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54723794076243660578140885 1282588923661960794800177)
                    ·
                      rfl

theorem cell23_7493499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 7].length) (baseStart_7493499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493499 prefixEnd_7493499 := by exact prefixLift 7493499
  have htrace : WordTrace (prefixWord ++ tailWord_7493499) baseStart_7493499 baseEnd_7493499 := by
    simpa [prefixWord, tailWord_7493499, baseEnd_7493499] using wordTrace_append hprefix tailTrace_7493499
  have hstable : (prefixWord ++ tailWord_7493499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493499).length < 2 ^ (prefixWord ++ tailWord_7493499).sum := by decide
  have hdescent : baseEnd_7493499 < baseStart_7493499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493534 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_7493534 : Nat := 118140960795 + 7493534 * 2 ^ 59
def prefixEnd_7493534 : Nat := 4983230072969 + 3 ^ 40 * 7493534 * 2
def baseEnd_7493534 : Nat := 3847784742808789747462871

theorem tailTrace_7493534 : CollatzResearch.WordTrace tailWord_7493534 prefixEnd_7493534 3847784742808789747462871 := by
  unfold tailWord_7493534
  simp only [CollatzResearch.WordTrace]
  refine ⟨34163954804276698320340957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182207758956142391041818437 34163954804276698320340957)
  ·
    refine ⟨12811483051603761870127859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34163954804276698320340957 12811483051603761870127859)
    ·
      refine ⟨19217224577405642805191789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12811483051603761870127859 19217224577405642805191789)
      ·
        refine ⟨7206459216527116051946921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19217224577405642805191789 7206459216527116051946921)
        ·
          refine ⟨5404844412395337038960191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7206459216527116051946921 5404844412395337038960191)
          ·
            refine ⟨8107266618593005558440287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5404844412395337038960191 8107266618593005558440287)
            ·
              refine ⟨12160899927889508337660431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8107266618593005558440287 12160899927889508337660431)
              ·
                refine ⟨18241349891834262506490647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12160899927889508337660431 18241349891834262506490647)
                ·
                  refine ⟨27362024837751393759735971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18241349891834262506490647 27362024837751393759735971)
                  ·
                    refine ⟨41043037256627090639603957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27362024837751393759735971 41043037256627090639603957)
                    ·
                      refine ⟨3847784742808789747462871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41043037256627090639603957 3847784742808789747462871)
                      ·
                        rfl

theorem cell23_7493534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_7493534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493534 prefixEnd_7493534 := by exact prefixLift 7493534
  have htrace : WordTrace (prefixWord ++ tailWord_7493534) baseStart_7493534 baseEnd_7493534 := by
    simpa [prefixWord, tailWord_7493534, baseEnd_7493534] using wordTrace_append hprefix tailTrace_7493534
  have hstable : (prefixWord ++ tailWord_7493534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493534).length < 2 ^ (prefixWord ++ tailWord_7493534).sum := by decide
  have hdescent : baseEnd_7493534 < baseStart_7493534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493576 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 9]
def baseStart_7493576 : Nat := 118140960795 + 7493576 * 2 ^ 59
def prefixEnd_7493576 : Nat := 4983230072969 + 3 ^ 40 * 7493576 * 2
def baseEnd_7493576 : Nat := 427534034332919842570853

theorem tailTrace_7493576 : CollatzResearch.WordTrace tailWord_7493576 prefixEnd_7493576 427534034332919842570853 := by
  unfold tailWord_7493576
  simp only [CollatzResearch.WordTrace]
  refine ⟨136656585150030713867878291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182208780200040951823837721 136656585150030713867878291)
  ·
    refine ⟨204984877725046070801817437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136656585150030713867878291 204984877725046070801817437)
    ·
      refine ⟨76869329146892276550681539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204984877725046070801817437 76869329146892276550681539)
      ·
        refine ⟨115303993720338414826022309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76869329146892276550681539 115303993720338414826022309)
        ·
          refine ⟨21619498822563452779879183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115303993720338414826022309 21619498822563452779879183)
          ·
            refine ⟨32429248233845179169818775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21619498822563452779879183 32429248233845179169818775)
            ·
              refine ⟨48643872350767768754728163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32429248233845179169818775 48643872350767768754728163)
              ·
                refine ⟨72965808526151653132092245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48643872350767768754728163 72965808526151653132092245)
                ·
                  refine ⟨427534034332919842570853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72965808526151653132092245 427534034332919842570853)
                  ·
                    rfl

theorem cell23_7493576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 9].length) (baseStart_7493576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493576 prefixEnd_7493576 := by exact prefixLift 7493576
  have htrace : WordTrace (prefixWord ++ tailWord_7493576) baseStart_7493576 baseEnd_7493576 := by
    simpa [prefixWord, tailWord_7493576, baseEnd_7493576] using wordTrace_append hprefix tailTrace_7493576
  have hstable : (prefixWord ++ tailWord_7493576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493576).length < 2 ^ (prefixWord ++ tailWord_7493576).sum := by decide
  have hdescent : baseEnd_7493576 < baseStart_7493576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493603 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 3]
def baseStart_7493603 : Nat := 118140960795 + 7493603 * 2 ^ 59
def prefixEnd_7493603 : Nat := 4983230072969 + 3 ^ 40 * 7493603 * 2
def baseEnd_7493603 : Nat := 3847820172973949977500053

theorem tailTrace_7493603 : CollatzResearch.WordTrace tailWord_7493603 prefixEnd_7493603 3847820172973949977500053 := by
  unfold tailWord_7493603
  simp only [CollatzResearch.WordTrace]
  refine ⟨273314155070963611346989463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182209436713975740897992975 273314155070963611346989463)
  ·
    refine ⟨409971232606445417020484195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273314155070963611346989463 409971232606445417020484195)
    ·
      refine ⟨614956848909668125530726293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409971232606445417020484195 614956848909668125530726293)
      ·
        refine ⟨28826102292640693384252795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 614956848909668125530726293 28826102292640693384252795)
        ·
          refine ⟨43239153438961040076379193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28826102292640693384252795 43239153438961040076379193)
          ·
            refine ⟨32429365079220780057284395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43239153438961040076379193 32429365079220780057284395)
            ·
              refine ⟨48644047618831170085926593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32429365079220780057284395 48644047618831170085926593)
              ·
                refine ⟨36483035714123377564444945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48644047618831170085926593 36483035714123377564444945)
                ·
                  refine ⟨27362276785592533173333709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36483035714123377564444945 27362276785592533173333709)
                  ·
                    refine ⟨10260853794597199940000141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27362276785592533173333709 10260853794597199940000141)
                    ·
                      refine ⟨3847820172973949977500053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10260853794597199940000141 3847820172973949977500053)
                      ·
                        rfl

theorem cell23_7493603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_7493603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493603 prefixEnd_7493603 := by exact prefixLift 7493603
  have htrace : WordTrace (prefixWord ++ tailWord_7493603) baseStart_7493603 baseEnd_7493603 := by
    simpa [prefixWord, tailWord_7493603, baseEnd_7493603] using wordTrace_append hprefix tailTrace_7493603
  have hstable : (prefixWord ++ tailWord_7493603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493603).length < 2 ^ (prefixWord ++ tailWord_7493603).sum := by decide
  have hdescent : baseEnd_7493603 < baseStart_7493603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493616 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 5]
def baseStart_7493616 : Nat := 118140960795 + 7493616 * 2 ^ 59
def prefixEnd_7493616 : Nat := 4983230072969 + 3 ^ 40 * 7493616 * 2
def baseEnd_7493616 : Nat := 3847826848222458426637493

theorem tailTrace_7493616 : CollatzResearch.WordTrace tailWord_7493616 prefixEnd_7493616 3847826848222458426637493 := by
  unfold tailWord_7493616
  simp only [CollatzResearch.WordTrace]
  refine ⟨136657314609958257283606351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182209752813277676378141801 136657314609958257283606351)
  ·
    refine ⟨204985971914937385925409527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136657314609958257283606351 204985971914937385925409527)
    ·
      refine ⟨307478957872406078888114291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204985971914937385925409527 307478957872406078888114291)
      ·
        refine ⟨461218436808609118332171437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307478957872406078888114291 461218436808609118332171437)
        ·
          refine ⟨172956913803228419374564289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461218436808609118332171437 172956913803228419374564289)
          ·
            refine ⟨129717685352421314530923217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172956913803228419374564289 129717685352421314530923217)
            ·
              refine ⟨97288264014315985898192413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129717685352421314530923217 97288264014315985898192413)
              ·
                refine ⟨36483099005368494711822155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97288264014315985898192413 36483099005368494711822155)
                ·
                  refine ⟨54724648508052742067733233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36483099005368494711822155 54724648508052742067733233)
                  ·
                    refine ⟨41043486381039556550799925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54724648508052742067733233 41043486381039556550799925)
                    ·
                      refine ⟨3847826848222458426637493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41043486381039556550799925 3847826848222458426637493)
                      ·
                        rfl

theorem cell23_7493616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_7493616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493616 prefixEnd_7493616 := by exact prefixLift 7493616
  have htrace : WordTrace (prefixWord ++ tailWord_7493616) baseStart_7493616 baseEnd_7493616 := by
    simpa [prefixWord, tailWord_7493616, baseEnd_7493616] using wordTrace_append hprefix tailTrace_7493616
  have hstable : (prefixWord ++ tailWord_7493616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493616).length < 2 ^ (prefixWord ++ tailWord_7493616).sum := by decide
  have hdescent : baseEnd_7493616 < baseStart_7493616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493643 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 4]
def baseStart_7493643 : Nat := 118140960795 + 7493643 * 2 ^ 59
def prefixEnd_7493643 : Nat := 4983230072969 + 3 ^ 40 * 7493643 * 2
def baseEnd_7493643 : Nat := 3847840712200129820999869

theorem tailTrace_7493643 : CollatzResearch.WordTrace tailWord_7493643 prefixEnd_7493643 3847840712200129820999869 := by
  unfold tailWord_7493643
  simp only [CollatzResearch.WordTrace]
  refine ⟨273315613990818698178445583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182210409327212465452297055 273315613990818698178445583)
  ·
    refine ⟨409973420986228047267668375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273315613990818698178445583 409973420986228047267668375)
    ·
      refine ⟨614960131479342070901502563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409973420986228047267668375 614960131479342070901502563)
      ·
        refine ⟨922440197219013106352253845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614960131479342070901502563 922440197219013106352253845)
        ·
          refine ⟨43239384244641239360261899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 922440197219013106352253845 43239384244641239360261899)
          ·
            refine ⟨64859076366961859040392849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43239384244641239360261899 64859076366961859040392849)
            ·
              refine ⟨48644307275221394280294637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64859076366961859040392849 48644307275221394280294637)
              ·
                refine ⟨18241615228208022855110489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48644307275221394280294637 18241615228208022855110489)
                ·
                  refine ⟨13681211421156017141332867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18241615228208022855110489 13681211421156017141332867)
                  ·
                    refine ⟨20521817131734025711999301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13681211421156017141332867 20521817131734025711999301)
                    ·
                      refine ⟨3847840712200129820999869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20521817131734025711999301 3847840712200129820999869)
                      ·
                        rfl

theorem cell23_7493643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 4].length) (baseStart_7493643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493643 prefixEnd_7493643 := by exact prefixLift 7493643
  have htrace : WordTrace (prefixWord ++ tailWord_7493643) baseStart_7493643 baseEnd_7493643 := by
    simpa [prefixWord, tailWord_7493643, baseEnd_7493643] using wordTrace_append hprefix tailTrace_7493643
  have hstable : (prefixWord ++ tailWord_7493643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493643).length < 2 ^ (prefixWord ++ tailWord_7493643).sum := by decide
  have hdescent : baseEnd_7493643 < baseStart_7493643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493660 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_7493660 : Nat := 118140960795 + 7493660 * 2 ^ 59
def prefixEnd_7493660 : Nat := 4983230072969 + 3 ^ 40 * 7493660 * 2
def baseEnd_7493660 : Nat := 3847849441371256254487291

theorem tailTrace_7493660 : CollatzResearch.WordTrace tailWord_7493660 prefixEnd_7493660 3847849441371256254487291 := by
  unfold tailWord_7493660
  simp only [CollatzResearch.WordTrace]
  refine ⟨136658117015878555040907217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182210822687838073387876289 136658117015878555040907217)
  ·
    refine ⟨102493587761908916280680413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136658117015878555040907217 102493587761908916280680413)
    ·
      refine ⟨38435095410715843605255155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102493587761908916280680413 38435095410715843605255155)
      ·
        refine ⟨57652643116073765407882733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38435095410715843605255155 57652643116073765407882733)
        ·
          refine ⟨21619741168527662027956025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57652643116073765407882733 21619741168527662027956025)
          ·
            refine ⟨16214805876395746520967019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21619741168527662027956025 16214805876395746520967019)
            ·
              refine ⟨24322208814593619781450529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16214805876395746520967019 24322208814593619781450529)
              ·
                refine ⟨18241656610945214836087897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24322208814593619781450529 18241656610945214836087897)
                ·
                  refine ⟨13681242458208911127065923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18241656610945214836087897 13681242458208911127065923)
                  ·
                    refine ⟨20521863687313366690598885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13681242458208911127065923 20521863687313366690598885)
                    ·
                      refine ⟨3847849441371256254487291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20521863687313366690598885 3847849441371256254487291)
                      ·
                        rfl

theorem cell23_7493660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_7493660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493660 prefixEnd_7493660 := by exact prefixLift 7493660
  have htrace : WordTrace (prefixWord ++ tailWord_7493660) baseStart_7493660 baseEnd_7493660 := by
    simpa [prefixWord, tailWord_7493660, baseEnd_7493660] using wordTrace_append hprefix tailTrace_7493660
  have hstable : (prefixWord ++ tailWord_7493660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493660).length < 2 ^ (prefixWord ++ tailWord_7493660).sum := by decide
  have hdescent : baseEnd_7493660 < baseStart_7493660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493697 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_7493697 : Nat := 118140960795 + 7493697 * 2 ^ 59
def prefixEnd_7493697 : Nat := 4983230072969 + 3 ^ 40 * 7493697 * 2
def baseEnd_7493697 : Nat := 3847868440155472609724621

theorem tailTrace_7493697 : CollatzResearch.WordTrace tailWord_7493697 prefixEnd_7493697 3847868440155472609724621 := by
  unfold tailWord_7493697
  simp only [CollatzResearch.WordTrace]
  refine ⟨273317583532623065400911345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182211722355082043600607563 273317583532623065400911345)
  ·
    refine ⟨204988187649467299050683509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273317583532623065400911345 204988187649467299050683509)
    ·
      refine ⟨19217642592137559286001579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204988187649467299050683509 19217642592137559286001579)
      ·
        refine ⟨28826463888206338929002369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19217642592137559286001579 28826463888206338929002369)
        ·
          refine ⟨21619847916154754196751777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28826463888206338929002369 21619847916154754196751777)
          ·
            refine ⟨16214885937116065647563833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21619847916154754196751777 16214885937116065647563833)
            ·
              refine ⟨12161164452837049235672875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16214885937116065647563833 12161164452837049235672875)
              ·
                refine ⟨18241746679255573853509313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12161164452837049235672875 18241746679255573853509313)
                ·
                  refine ⟨13681310009441680390131985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18241746679255573853509313 13681310009441680390131985)
                  ·
                    refine ⟨10260982507081260292598989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13681310009441680390131985 10260982507081260292598989)
                    ·
                      refine ⟨3847868440155472609724621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10260982507081260292598989 3847868440155472609724621)
                      ·
                        rfl

theorem cell23_7493697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_7493697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493697 prefixEnd_7493697 := by exact prefixLift 7493697
  have htrace : WordTrace (prefixWord ++ tailWord_7493697) baseStart_7493697 baseEnd_7493697 := by
    simpa [prefixWord, tailWord_7493697, baseEnd_7493697] using wordTrace_append hprefix tailTrace_7493697
  have hstable : (prefixWord ++ tailWord_7493697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493697).length < 2 ^ (prefixWord ++ tailWord_7493697).sum := by decide
  have hdescent : baseEnd_7493697 < baseStart_7493697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493743 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 1, 6]
def baseStart_7493743 : Nat := 118140960795 + 7493743 * 2 ^ 59
def prefixEnd_7493743 : Nat := 4983230072969 + 3 ^ 40 * 7493743 * 2
def baseEnd_7493743 : Nat := 1282630686755193143249803

theorem tailTrace_7493743 : CollatzResearch.WordTrace tailWord_7493743 prefixEnd_7493743 1282630686755193143249803 := by
  unfold tailWord_7493743
  simp only [CollatzResearch.WordTrace]
  refine ⟨273319261290456415257085883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182212840860304276838057255 273319261290456415257085883)
  ·
    refine ⟨409978891935684622885628825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273319261290456415257085883 409978891935684622885628825)
    ·
      refine ⟨307484168951763467164221619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409978891935684622885628825 307484168951763467164221619)
      ·
        refine ⟨461226253427645200746332429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307484168951763467164221619 461226253427645200746332429)
        ·
          refine ⟨172959845035366950279874661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461226253427645200746332429 172959845035366950279874661)
          ·
            refine ⟨32429970944131303177476499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172959845035366950279874661 32429970944131303177476499)
            ·
              refine ⟨48644956416196954766214749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32429970944131303177476499 48644956416196954766214749)
              ·
                refine ⟨18241858656073858037330531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48644956416196954766214749 18241858656073858037330531)
                ·
                  refine ⟨27362787984110787055995797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18241858656073858037330531 27362787984110787055995797)
                  ·
                    refine ⟨1282630686755193143249803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27362787984110787055995797 1282630686755193143249803)
                    ·
                      rfl

theorem cell23_7493743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 6].length) (baseStart_7493743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493743 prefixEnd_7493743 := by exact prefixLift 7493743
  have htrace : WordTrace (prefixWord ++ tailWord_7493743) baseStart_7493743 baseEnd_7493743 := by
    simpa [prefixWord, tailWord_7493743, baseEnd_7493743] using wordTrace_append hprefix tailTrace_7493743
  have hstable : (prefixWord ++ tailWord_7493743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493743).length < 2 ^ (prefixWord ++ tailWord_7493743).sum := by decide
  have hdescent : baseEnd_7493743 < baseStart_7493743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493761 : List Nat := [1, 2, 4, 2, 3, 1, 2, 3, 1, 1, 3]
def baseStart_7493761 : Nat := 118140960795 + 7493761 * 2 ^ 59
def prefixEnd_7493761 : Nat := 4983230072969 + 3 ^ 40 * 7493761 * 2
def baseEnd_7493761 : Nat := 3847901302917360359324327

theorem tailTrace_7493761 : CollatzResearch.WordTrace tailWord_7493761 prefixEnd_7493761 3847901302917360359324327 := by
  unfold tailWord_7493761
  simp only [CollatzResearch.WordTrace]
  refine ⟨273319917804391204331241137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182213278536260802887494091 273319917804391204331241137)
  ·
    refine ⟨204989938353293403248430853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273319917804391204331241137 204989938353293403248430853)
    ·
      refine ⟨38435613441242513109080785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204989938353293403248430853 38435613441242513109080785)
      ·
        refine ⟨28826710080931884831810589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38435613441242513109080785 28826710080931884831810589)
        ·
          refine ⟨10810016280349456811928971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28826710080931884831810589 10810016280349456811928971)
          ·
            refine ⟨16215024420524185217893457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10810016280349456811928971 16215024420524185217893457)
            ·
              refine ⟨12161268315393138913420093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16215024420524185217893457 12161268315393138913420093)
              ·
                refine ⟨4560475618272427092532535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12161268315393138913420093 4560475618272427092532535)
                ·
                  refine ⟨6840713427408640638798803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4560475618272427092532535 6840713427408640638798803)
                  ·
                    refine ⟨10261070141112960958198205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6840713427408640638798803 10261070141112960958198205)
                    ·
                      refine ⟨3847901302917360359324327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10261070141112960958198205 3847901302917360359324327)
                      ·
                        rfl

theorem cell23_7493761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_7493761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493761 prefixEnd_7493761 := by exact prefixLift 7493761
  have htrace : WordTrace (prefixWord ++ tailWord_7493761) baseStart_7493761 baseEnd_7493761 := by
    simpa [prefixWord, tailWord_7493761, baseEnd_7493761] using wordTrace_append hprefix tailTrace_7493761
  have hstable : (prefixWord ++ tailWord_7493761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493761).length < 2 ^ (prefixWord ++ tailWord_7493761).sum := by decide
  have hdescent : baseEnd_7493761 < baseStart_7493761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493767 : List Nat := [1, 1, 4, 2, 1, 1, 6, 1, 1, 1, 4]
def baseStart_7493767 : Nat := 118140960795 + 7493767 * 2 ^ 59
def prefixEnd_7493767 : Nat := 4983230072969 + 3 ^ 40 * 7493767 * 2
def baseEnd_7493767 : Nat := 3847904383801287335849299

theorem tailTrace_7493767 : CollatzResearch.WordTrace tailWord_7493767 prefixEnd_7493767 3847904383801287335849299 := by
  unfold tailWord_7493767
  simp only [CollatzResearch.WordTrace]
  refine ⟨273320136642369467355959555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182213424428246311570639703 273320136642369467355959555)
  ·
    refine ⟨409980204963554201033939333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273320136642369467355959555 409980204963554201033939333)
    ·
      refine ⟨76871288430666412693863625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409980204963554201033939333 76871288430666412693863625)
      ·
        refine ⟨57653466322999809520397719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76871288430666412693863625 57653466322999809520397719)
        ·
          refine ⟨86480199484499714280596579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57653466322999809520397719 86480199484499714280596579)
          ·
            refine ⟨129720299226749571420894869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86480199484499714280596579 129720299226749571420894869)
            ·
              refine ⟨6080639026253886160354447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129720299226749571420894869 6080639026253886160354447)
              ·
                refine ⟨9120958539380829240531671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6080639026253886160354447 9120958539380829240531671)
                ·
                  refine ⟨13681437809071243860797507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9120958539380829240531671 13681437809071243860797507)
                  ·
                    refine ⟨20522156713606865791196261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13681437809071243860797507 20522156713606865791196261)
                    ·
                      refine ⟨3847904383801287335849299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20522156713606865791196261 3847904383801287335849299)
                      ·
                        rfl

theorem cell23_7493767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_7493767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493767 prefixEnd_7493767 := by exact prefixLift 7493767
  have htrace : WordTrace (prefixWord ++ tailWord_7493767) baseStart_7493767 baseEnd_7493767 := by
    simpa [prefixWord, tailWord_7493767, baseEnd_7493767] using wordTrace_append hprefix tailTrace_7493767
  have hstable : (prefixWord ++ tailWord_7493767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493767).length < 2 ^ (prefixWord ++ tailWord_7493767).sum := by decide
  have hdescent : baseEnd_7493767 < baseStart_7493767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493812 : List Nat := [2, 5, 3, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_7493812 : Nat := 118140960795 + 7493812 * 2 ^ 59
def prefixEnd_7493812 : Nat := 4983230072969 + 3 ^ 40 * 7493812 * 2
def baseEnd_7493812 : Nat := 3847927490430739659786593

theorem tailTrace_7493812 : CollatzResearch.WordTrace tailWord_7493812 prefixEnd_7493812 3847927490430739659786593 := by
  unfold tailWord_7493812
  simp only [CollatzResearch.WordTrace]
  refine ⟨136660888963603220020673845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182214518618137626694231793 136660888963603220020673845)
  ·
    refine ⟨12811958340337801876938173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136660888963603220020673845 12811958340337801876938173)
    ·
      refine ⟨4804484377626675703851815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12811958340337801876938173 4804484377626675703851815)
      ·
        refine ⟨7206726566440013555777723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4804484377626675703851815 7206726566440013555777723)
        ·
          refine ⟨10810089849660020333666585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7206726566440013555777723 10810089849660020333666585)
          ·
            refine ⟨8107567387245015250249939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10810089849660020333666585 8107567387245015250249939)
            ·
              refine ⟨12161351080867522875374909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8107567387245015250249939 12161351080867522875374909)
              ·
                refine ⟨4560506655325321078265591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12161351080867522875374909 4560506655325321078265591)
                ·
                  refine ⟨6840759982987981617398387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4560506655325321078265591 6840759982987981617398387)
                  ·
                    refine ⟨10261139974481972426097581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6840759982987981617398387 10261139974481972426097581)
                    ·
                      refine ⟨3847927490430739659786593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10261139974481972426097581 3847927490430739659786593)
                      ·
                        rfl

theorem cell23_7493812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_7493812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493812 prefixEnd_7493812 := by exact prefixLift 7493812
  have htrace : WordTrace (prefixWord ++ tailWord_7493812) baseStart_7493812 baseEnd_7493812 := by
    simpa [prefixWord, tailWord_7493812, baseEnd_7493812] using wordTrace_append hprefix tailTrace_7493812
  have hstable : (prefixWord ++ tailWord_7493812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493812).length < 2 ^ (prefixWord ++ tailWord_7493812).sum := by decide
  have hdescent : baseEnd_7493812 < baseStart_7493812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493823 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 4]
def baseStart_7493823 : Nat := 118140960795 + 7493823 * 2 ^ 59
def prefixEnd_7493823 : Nat := 4983230072969 + 3 ^ 40 * 7493823 * 2
def baseEnd_7493823 : Nat := 3847933138717939116749041

theorem tailTrace_7493823 : CollatzResearch.WordTrace tailWord_7493823 prefixEnd_7493823 3847933138717939116749041 := by
  unfold tailWord_7493823
  simp only [CollatzResearch.WordTrace]
  refine ⟨273322179130166588919998123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182214786086777725946665415 273322179130166588919998123)
  ·
    refine ⟨409983268695249883379997185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273322179130166588919998123 409983268695249883379997185)
    ·
      refine ⟨307487451521437412534997889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409983268695249883379997185 307487451521437412534997889)
      ·
        refine ⟨230615588641078059401248417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307487451521437412534997889 230615588641078059401248417)
        ·
          refine ⟨172961691480808544550936313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230615588641078059401248417 172961691480808544550936313)
          ·
            refine ⟨129721268610606408413202235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172961691480808544550936313 129721268610606408413202235)
            ·
              refine ⟨194581902915909612619803353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129721268610606408413202235 194581902915909612619803353)
              ·
                refine ⟨145936427186932209464852515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194581902915909612619803353 145936427186932209464852515)
                ·
                  refine ⟨218904640780398314197278773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145936427186932209464852515 218904640780398314197278773)
                  ·
                    refine ⟨20522310073162341955994885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 218904640780398314197278773 20522310073162341955994885)
                    ·
                      refine ⟨3847933138717939116749041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20522310073162341955994885 3847933138717939116749041)
                      ·
                        rfl

theorem cell23_7493823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_7493823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493823 prefixEnd_7493823 := by exact prefixLift 7493823
  have htrace : WordTrace (prefixWord ++ tailWord_7493823) baseStart_7493823 baseEnd_7493823 := by
    simpa [prefixWord, tailWord_7493823, baseEnd_7493823] using wordTrace_append hprefix tailTrace_7493823
  have hstable : (prefixWord ++ tailWord_7493823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493823).length < 2 ^ (prefixWord ++ tailWord_7493823).sum := by decide
  have hdescent : baseEnd_7493823 < baseStart_7493823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493833 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 2, 6]
def baseStart_7493833 : Nat := 118140960795 + 7493833 * 2 ^ 59
def prefixEnd_7493833 : Nat := 4983230072969 + 3 ^ 40 * 7493833 * 2
def baseEnd_7493833 : Nat := 1282646091174828025874665

theorem tailTrace_7493833 : CollatzResearch.WordTrace tailWord_7493833 prefixEnd_7493833 1282646091174828025874665 := by
  unfold tailWord_7493833
  simp only [CollatzResearch.WordTrace]
  refine ⟨273322543860130360627862153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182215029240086907085241435 273322543860130360627862153)
  ·
    refine ⟨204991907895097770470896615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273322543860130360627862153 204991907895097770470896615)
    ·
      refine ⟨307487861842646655706344923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204991907895097770470896615 307487861842646655706344923)
      ·
        refine ⟨461231792763969983559517385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307487861842646655706344923 461231792763969983559517385)
        ·
          refine ⟨345923844572977487669638039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461231792763969983559517385 345923844572977487669638039)
          ·
            refine ⟨518885766859466231504457059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345923844572977487669638039 518885766859466231504457059)
            ·
              refine ⟨778328650289199347256685589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518885766859466231504457059 778328650289199347256685589)
              ·
                refine ⟨36484155482306219402657137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 778328650289199347256685589 36484155482306219402657137)
                ·
                  refine ⟨27363116611729664551992853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36484155482306219402657137 27363116611729664551992853)
                  ·
                    refine ⟨1282646091174828025874665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27363116611729664551992853 1282646091174828025874665)
                    ·
                      rfl

theorem cell23_7493833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 6].length) (baseStart_7493833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493833 prefixEnd_7493833 := by exact prefixLift 7493833
  have htrace : WordTrace (prefixWord ++ tailWord_7493833) baseStart_7493833 baseEnd_7493833 := by
    simpa [prefixWord, tailWord_7493833, baseEnd_7493833] using wordTrace_append hprefix tailTrace_7493833
  have hstable : (prefixWord ++ tailWord_7493833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493833).length < 2 ^ (prefixWord ++ tailWord_7493833).sum := by decide
  have hdescent : baseEnd_7493833 < baseStart_7493833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
