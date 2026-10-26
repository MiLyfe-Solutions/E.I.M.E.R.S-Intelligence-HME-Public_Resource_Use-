import V185TrunkScan22Chunk226

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2023803 : List Nat := [1, 1, 1, 1, 1, 9, 2, 1, 5]
def baseStart_2023803 : Nat := 118140960795 + 2023803 * 2 ^ 59
def prefixEnd_2023803 : Nat := 4983230072969 + 3 ^ 40 * 2023803 * 2
def baseEnd_2023803 : Nat := 230929708669166798923379

theorem tailTrace_2023803 : CollatzResearch.WordTrace tailWord_2023803 prefixEnd_2023803 230929708669166798923379 := by
  unfold tailWord_2023803
  simp only [CollatzResearch.WordTrace]
  refine ⟨73814159487114843879860063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49209439658076562586573375 73814159487114843879860063)
  ·
    refine ⟨110721239230672265819790095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73814159487114843879860063 110721239230672265819790095)
    ·
      refine ⟨166081858846008398729685143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110721239230672265819790095 166081858846008398729685143)
      ·
        refine ⟨249122788269012598094527715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166081858846008398729685143 249122788269012598094527715)
        ·
          refine ⟨373684182403518897141791573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249122788269012598094527715 373684182403518897141791573)
          ·
            refine ⟨2189555756270618537940185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 373684182403518897141791573 2189555756270618537940185)
            ·
              refine ⟨1642166817202963903455139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2189555756270618537940185 1642166817202963903455139)
              ·
                refine ⟨2463250225804445855182709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642166817202963903455139 2463250225804445855182709)
                ·
                  refine ⟨230929708669166798923379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2463250225804445855182709 230929708669166798923379)
                  ·
                    rfl

theorem cell22_2023803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 5].length) (baseStart_2023803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023803 prefixEnd_2023803 := by exact prefixLift 2023803
  have htrace : WordTrace (prefixWord ++ tailWord_2023803) baseStart_2023803 baseEnd_2023803 := by
    simpa [prefixWord, tailWord_2023803, baseEnd_2023803] using wordTrace_append hprefix tailTrace_2023803
  have hstable : (prefixWord ++ tailWord_2023803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023803).length < 2 ^ (prefixWord ++ tailWord_2023803).sum := by decide
  have hdescent : baseEnd_2023803 < baseStart_2023803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023816 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 3, 4]
def baseStart_2023816 : Nat := 118140960795 + 2023816 * 2 ^ 59
def prefixEnd_2023816 : Nat := 4983230072969 + 3 ^ 40 * 2023816 * 2
def baseEnd_2023816 : Nat := 692793576173172696195097

theorem tailTrace_2023816 : CollatzResearch.WordTrace tailWord_2023816 prefixEnd_2023816 692793576173172696195097 := by
  unfold tailWord_2023816
  simp only [CollatzResearch.WordTrace]
  refine ⟨36907316818033873550041651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49209755757378498066722201 36907316818033873550041651)
  ·
    refine ⟨55360975227050810325062477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36907316818033873550041651 55360975227050810325062477)
    ·
      refine ⟨20760365710144053871898429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55360975227050810325062477 20760365710144053871898429)
      ·
        refine ⟨7785137141304020201961911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20760365710144053871898429 7785137141304020201961911)
        ·
          refine ⟨11677705711956030302942867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7785137141304020201961911 11677705711956030302942867)
          ·
            refine ⟨17516558567934045454414301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11677705711956030302942867 17516558567934045454414301)
            ·
              refine ⟨6568709462975267045405363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17516558567934045454414301 6568709462975267045405363)
              ·
                refine ⟨9853064194462900568108045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6568709462975267045405363 9853064194462900568108045)
                ·
                  refine ⟨3694899072923587713040517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9853064194462900568108045 3694899072923587713040517)
                  ·
                    refine ⟨692793576173172696195097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3694899072923587713040517 692793576173172696195097)
                    ·
                      rfl

theorem cell22_2023816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_2023816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023816 prefixEnd_2023816 := by exact prefixLift 2023816
  have htrace : WordTrace (prefixWord ++ tailWord_2023816) baseStart_2023816 baseEnd_2023816 := by
    simpa [prefixWord, tailWord_2023816, baseEnd_2023816] using wordTrace_append hprefix tailTrace_2023816
  have hstable : (prefixWord ++ tailWord_2023816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023816).length < 2 ^ (prefixWord ++ tailWord_2023816).sum := by decide
  have hdescent : baseEnd_2023816 < baseStart_2023816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023833 : List Nat := [1, 2, 1, 2, 1, 4, 5, 1, 1, 4]
def baseStart_2023833 : Nat := 118140960795 + 2023833 * 2 ^ 59
def prefixEnd_2023833 : Nat := 4983230072969 + 3 ^ 40 * 2023833 * 2
def baseEnd_2023833 : Nat := 692799395620590318520045

theorem tailTrace_2023833 : CollatzResearch.WordTrace tailWord_2023833 prefixEnd_2023833 692799395620590318520045 := by
  unfold tailWord_2023833
  simp only [CollatzResearch.WordTrace]
  refine ⟨73815253677006159003452153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49210169118004106002301435 73815253677006159003452153)
  ·
    refine ⟨55361440257754619252589115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73815253677006159003452153 55361440257754619252589115)
    ·
      refine ⟨83042160386631928878883673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55361440257754619252589115 83042160386631928878883673)
      ·
        refine ⟨62281620289973946659162755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83042160386631928878883673 62281620289973946659162755)
        ·
          refine ⟨93422430434960919988744133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62281620289973946659162755 93422430434960919988744133)
          ·
            refine ⟨17516705706555172497889525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93422430434960919988744133 17516705706555172497889525)
            ·
              refine ⟨1642191159989547421677143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17516705706555172497889525 1642191159989547421677143)
              ·
                refine ⟨2463286739984321132515715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642191159989547421677143 2463286739984321132515715)
                ·
                  refine ⟨3694930109976481698773573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2463286739984321132515715 3694930109976481698773573)
                  ·
                    refine ⟨692799395620590318520045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3694930109976481698773573 692799395620590318520045)
                    ·
                      rfl

theorem cell22_2023833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 1, 4].length) (baseStart_2023833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023833 prefixEnd_2023833 := by exact prefixLift 2023833
  have htrace : WordTrace (prefixWord ++ tailWord_2023833) baseStart_2023833 baseEnd_2023833 := by
    simpa [prefixWord, tailWord_2023833, baseEnd_2023833] using wordTrace_append hprefix tailTrace_2023833
  have hstable : (prefixWord ++ tailWord_2023833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023833).length < 2 ^ (prefixWord ++ tailWord_2023833).sum := by decide
  have hdescent : baseEnd_2023833 < baseStart_2023833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023841 : List Nat := [1, 2, 3, 5, 2, 1, 2, 2, 1, 3]
def baseStart_2023841 : Nat := 118140960795 + 2023841 * 2 ^ 59
def prefixEnd_2023841 : Nat := 4983230072969 + 3 ^ 40 * 2023841 * 2
def baseEnd_2023841 : Nat := 692802134184080964320021

theorem tailTrace_2023841 : CollatzResearch.WordTrace tailWord_2023841 prefixEnd_2023841 692802134184080964320021 := by
  unfold tailWord_2023841
  simp only [CollatzResearch.WordTrace]
  refine ⟨73815545460977176369743377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49210363640651450913162251 73815545460977176369743377)
  ·
    refine ⟨55361659095732882277307533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73815545460977176369743377 55361659095732882277307533)
    ·
      refine ⟨20760622160899830853990325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55361659095732882277307533 20760622160899830853990325)
      ·
        refine ⟨1946308327584359142561593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20760622160899830853990325 1946308327584359142561593)
        ·
          refine ⟨1459731245688269356921195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1946308327584359142561593 1459731245688269356921195)
          ·
            refine ⟨2189596868532404035381793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459731245688269356921195 2189596868532404035381793)
            ·
              refine ⟨1642197651399303026536345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2189596868532404035381793 1642197651399303026536345)
              ·
                refine ⟨1231648238549477269902259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1642197651399303026536345 1231648238549477269902259)
                ·
                  refine ⟨1847472357824215904853389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231648238549477269902259 1847472357824215904853389)
                  ·
                    refine ⟨692802134184080964320021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1847472357824215904853389 692802134184080964320021)
                    ·
                      rfl

theorem cell22_2023841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_2023841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023841 prefixEnd_2023841 := by exact prefixLift 2023841
  have htrace : WordTrace (prefixWord ++ tailWord_2023841) baseStart_2023841 baseEnd_2023841 := by
    simpa [prefixWord, tailWord_2023841, baseEnd_2023841] using wordTrace_append hprefix tailTrace_2023841
  have hstable : (prefixWord ++ tailWord_2023841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023841).length < 2 ^ (prefixWord ++ tailWord_2023841).sum := by decide
  have hdescent : baseEnd_2023841 < baseStart_2023841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023863 : List Nat := [1, 1, 3, 1, 3, 3, 2, 3, 2, 3]
def baseStart_2023863 : Nat := 118140960795 + 2023863 * 2 ^ 59
def prefixEnd_2023863 : Nat := 4983230072969 + 3 ^ 40 * 2023863 * 2
def baseEnd_2023863 : Nat := 692809665233680240269953

theorem tailTrace_2023863 : CollatzResearch.WordTrace tailWord_2023863 prefixEnd_2023863 692809665233680240269953 := by
  unfold tailWord_2023863
  simp only [CollatzResearch.WordTrace]
  refine ⟨73816347866897474127044243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49210898577931649418029495 73816347866897474127044243)
  ·
    refine ⟨110724521800346211190566365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73816347866897474127044243 110724521800346211190566365)
    ·
      refine ⟨41521695675129829196462387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110724521800346211190566365 41521695675129829196462387)
      ·
        refine ⟨62282543512694743794693581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41521695675129829196462387 62282543512694743794693581)
        ·
          refine ⟨23355953817260528923010093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62282543512694743794693581 23355953817260528923010093)
          ·
            refine ⟨8758482681472698346128785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23355953817260528923010093 8758482681472698346128785)
            ·
              refine ⟨6568862011104523759596589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8758482681472698346128785 6568862011104523759596589)
              ·
                refine ⟨2463323254164196409848721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6568862011104523759596589 2463323254164196409848721)
                ·
                  refine ⟨1847492440623147307386541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2463323254164196409848721 1847492440623147307386541)
                  ·
                    refine ⟨692809665233680240269953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1847492440623147307386541 692809665233680240269953)
                    ·
                      rfl

theorem cell22_2023863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_2023863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023863 prefixEnd_2023863 := by exact prefixLift 2023863
  have htrace : WordTrace (prefixWord ++ tailWord_2023863) baseStart_2023863 baseEnd_2023863 := by
    simpa [prefixWord, tailWord_2023863, baseEnd_2023863] using wordTrace_append hprefix tailTrace_2023863
  have hstable : (prefixWord ++ tailWord_2023863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023863).length < 2 ^ (prefixWord ++ tailWord_2023863).sum := by decide
  have hdescent : baseEnd_2023863 < baseStart_2023863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023959 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 3, 3]
def baseStart_2023959 : Nat := 118140960795 + 2023959 * 2 ^ 59
def prefixEnd_2023959 : Nat := 4983230072969 + 3 ^ 40 * 2023959 * 2
def baseEnd_2023959 : Nat := 692842527995567989869659

theorem tailTrace_2023959 : CollatzResearch.WordTrace tailWord_2023959 prefixEnd_2023959 692842527995567989869659 := by
  unfold tailWord_2023959
  simp only [CollatzResearch.WordTrace]
  refine ⟨73819849274549682522538931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49213232849699788348359287 73819849274549682522538931)
  ·
    refine ⟨110729773911824523783808397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73819849274549682522538931 110729773911824523783808397)
    ·
      refine ⟨41523665216934196418928149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110729773911824523783808397 41523665216934196418928149)
      ·
        refine ⟨1946421807043790457137257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41523665216934196418928149 1946421807043790457137257)
        ·
          refine ⟨1459816355282842842852943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1946421807043790457137257 1459816355282842842852943)
          ·
            refine ⟨2189724532924264264279415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459816355282842842852943 2189724532924264264279415)
            ·
              refine ⟨3284586799386396396419123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189724532924264264279415 3284586799386396396419123)
              ·
                refine ⟨4926880199079594594628685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284586799386396396419123 4926880199079594594628685)
                ·
                  refine ⟨1847580074654847972985757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4926880199079594594628685 1847580074654847972985757)
                  ·
                    refine ⟨692842527995567989869659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1847580074654847972985757 692842527995567989869659)
                    ·
                      rfl

theorem cell22_2023959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_2023959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023959 prefixEnd_2023959 := by exact prefixLift 2023959
  have htrace : WordTrace (prefixWord ++ tailWord_2023959) baseStart_2023959 baseEnd_2023959 := by
    simpa [prefixWord, tailWord_2023959, baseEnd_2023959] using wordTrace_append hprefix tailTrace_2023959
  have hstable : (prefixWord ++ tailWord_2023959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023959).length < 2 ^ (prefixWord ++ tailWord_2023959).sum := by decide
  have hdescent : baseEnd_2023959 < baseStart_2023959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024017 : List Nat := [1, 2, 2, 1, 3, 5, 2, 2, 4]
def baseStart_2024017 : Nat := 118140960795 + 2024017 * 2 ^ 59
def prefixEnd_2024017 : Nat := 4983230072969 + 3 ^ 40 * 2024017 * 2
def baseEnd_2024017 : Nat := 230954127526958390639827

theorem tailTrace_2024017 : CollatzResearch.WordTrace tailWord_2024017 prefixEnd_2024017 230954127526958390639827 := by
  unfold tailWord_2024017
  simp only [CollatzResearch.WordTrace]
  refine ⟨73821964708339558428150305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49214643138893038952100203 73821964708339558428150305)
  ·
    refine ⟨55366473531254668821112729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73821964708339558428150305 55366473531254668821112729)
    ·
      refine ⟨41524855148441001615834547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55366473531254668821112729 41524855148441001615834547)
      ·
        refine ⟨62287282722661502423751821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41524855148441001615834547 62287282722661502423751821)
        ·
          refine ⟨23357731020998063408906933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62287282722661502423751821 23357731020998063408906933)
          ·
            refine ⟨2189787283218568444585025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23357731020998063408906933 2189787283218568444585025)
            ·
              refine ⟨1642340462413926333438769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2189787283218568444585025 1642340462413926333438769)
              ·
                refine ⟨1231755346810444750079077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1642340462413926333438769 1231755346810444750079077)
                ·
                  refine ⟨230954127526958390639827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1231755346810444750079077 230954127526958390639827)
                  ·
                    rfl

theorem cell22_2024017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 4].length) (baseStart_2024017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024017 prefixEnd_2024017 := by exact prefixLift 2024017
  have htrace : WordTrace (prefixWord ++ tailWord_2024017) baseStart_2024017 baseEnd_2024017 := by
    simpa [prefixWord, tailWord_2024017, baseEnd_2024017] using wordTrace_append hprefix tailTrace_2024017
  have hstable : (prefixWord ++ tailWord_2024017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024017).length < 2 ^ (prefixWord ++ tailWord_2024017).sum := by decide
  have hdescent : baseEnd_2024017 < baseStart_2024017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024026 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_2024026 : Nat := 118140960795 + 2024026 * 2 ^ 59
def prefixEnd_2024026 : Nat := 4983230072969 + 3 ^ 40 * 2024026 * 2
def baseEnd_2024026 : Nat := 692865463464802148444453

theorem tailTrace_2024026 : CollatzResearch.WordTrace tailWord_2024026 prefixEnd_2024026 692865463464802148444453 := by
  unfold tailWord_2024026
  simp only [CollatzResearch.WordTrace]
  refine ⟨18455573241326738241306983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49214861976871301976818621 18455573241326738241306983)
  ·
    refine ⟨27683359861990107361960475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18455573241326738241306983 27683359861990107361960475)
    ·
      refine ⟨41525039792985161042940713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27683359861990107361960475 41525039792985161042940713)
      ·
        refine ⟨31143779844738870782205535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41525039792985161042940713 31143779844738870782205535)
        ·
          refine ⟨46715669767108306173308303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31143779844738870782205535 46715669767108306173308303)
          ·
            refine ⟨70073504650662459259962455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46715669767108306173308303 70073504650662459259962455)
            ·
              refine ⟨105110256975993688889943683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70073504650662459259962455 105110256975993688889943683)
              ·
                refine ⟨157665385463990533334915525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105110256975993688889943683 157665385463990533334915525)
                ·
                  refine ⟨29562259774498225000296661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157665385463990533334915525 29562259774498225000296661)
                  ·
                    refine ⟨692865463464802148444453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29562259774498225000296661 692865463464802148444453)
                    ·
                      rfl

theorem cell22_2024026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_2024026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024026 prefixEnd_2024026 := by exact prefixLift 2024026
  have htrace : WordTrace (prefixWord ++ tailWord_2024026) baseStart_2024026 baseEnd_2024026 := by
    simpa [prefixWord, tailWord_2024026, baseEnd_2024026] using wordTrace_append hprefix tailTrace_2024026
  have hstable : (prefixWord ++ tailWord_2024026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024026).length < 2 ^ (prefixWord ++ tailWord_2024026).sum := by decide
  have hdescent : baseEnd_2024026 < baseStart_2024026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024041 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 4, 6]
def baseStart_2024041 : Nat := 118140960795 + 2024041 * 2 ^ 59
def prefixEnd_2024041 : Nat := 4983230072969 + 3 ^ 40 * 2024041 * 2
def baseEnd_2024041 : Nat := 692870598271347109319407

theorem tailTrace_2024041 : CollatzResearch.WordTrace tailWord_2024041 prefixEnd_2024041 692870598271347109319407 := by
  unfold tailWord_2024041
  simp only [CollatzResearch.WordTrace]
  refine ⟨73822840060252610527023977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49215226706835073684682651 73822840060252610527023977)
  ·
    refine ⟨55367130045189457895267983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73822840060252610527023977 55367130045189457895267983)
    ·
      refine ⟨83050695067784186842901975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55367130045189457895267983 83050695067784186842901975)
      ·
        refine ⟨124576042601676280264352963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83050695067784186842901975 124576042601676280264352963)
        ·
          refine ⟨186864063902514420396529445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124576042601676280264352963 186864063902514420396529445)
          ·
            refine ⟨35037011981721453824349271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186864063902514420396529445 35037011981721453824349271)
            ·
              refine ⟨52555517972582180736523907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35037011981721453824349271 52555517972582180736523907)
              ·
                refine ⟨78833276958873271104785861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52555517972582180736523907 78833276958873271104785861)
                ·
                  refine ⟨14781239429788738332147349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78833276958873271104785861 14781239429788738332147349)
                  ·
                    refine ⟨692870598271347109319407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14781239429788738332147349 692870598271347109319407)
                    ·
                      rfl

theorem cell22_2024041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_2024041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024041 prefixEnd_2024041 := by exact prefixLift 2024041
  have htrace : WordTrace (prefixWord ++ tailWord_2024041) baseStart_2024041 baseEnd_2024041 := by
    simpa [prefixWord, tailWord_2024041, baseEnd_2024041] using wordTrace_append hprefix tailTrace_2024041
  have hstable : (prefixWord ++ tailWord_2024041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024041).length < 2 ^ (prefixWord ++ tailWord_2024041).sum := by decide
  have hdescent : baseEnd_2024041 < baseStart_2024041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024045 : List Nat := [1, 5, 1, 1, 3, 2, 3, 6]
def baseStart_2024045 : Nat := 118140960795 + 2024045 * 2 ^ 59
def prefixEnd_2024045 : Nat := 4983230072969 + 3 ^ 40 * 2024045 * 2
def baseEnd_2024045 : Nat := 76985774172565825802155

theorem tailTrace_2024045 : CollatzResearch.WordTrace tailWord_2024045 prefixEnd_2024045 76985774172565825802155 := by
  unfold tailWord_2024045
  simp only [CollatzResearch.WordTrace]
  refine ⟨73822985952238119210169589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49215323968158746140113059 73822985952238119210169589)
  ·
    refine ⟨6920904933022323675953399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73822985952238119210169589 6920904933022323675953399)
    ·
      refine ⟨10381357399533485513930099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6920904933022323675953399 10381357399533485513930099)
      ·
        refine ⟨15572036099300228270895149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10381357399533485513930099 15572036099300228270895149)
        ·
          refine ⟨5839513537237585601585681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15572036099300228270895149 5839513537237585601585681)
          ·
            refine ⟨4379635152928189201189261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5839513537237585601585681 4379635152928189201189261)
            ·
              refine ⟨1642363182348070950445973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4379635152928189201189261 1642363182348070950445973)
              ·
                refine ⟨76985774172565825802155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1642363182348070950445973 76985774172565825802155)
                ·
                  rfl

theorem cell22_2024045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 6].length) (baseStart_2024045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024045 prefixEnd_2024045 := by exact prefixLift 2024045
  have htrace : WordTrace (prefixWord ++ tailWord_2024045) baseStart_2024045 baseEnd_2024045 := by
    simpa [prefixWord, tailWord_2024045, baseEnd_2024045] using wordTrace_append hprefix tailTrace_2024045
  have hstable : (prefixWord ++ tailWord_2024045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024045).length < 2 ^ (prefixWord ++ tailWord_2024045).sum := by decide
  have hdescent : baseEnd_2024045 < baseStart_2024045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024056 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 9]
def baseStart_2024056 : Nat := 118140960795 + 2024056 * 2 ^ 59
def prefixEnd_2024056 : Nat := 4983230072969 + 3 ^ 40 * 2024056 * 2
def baseEnd_2024056 : Nat := 230958577692630690064787

theorem tailTrace_2024056 : CollatzResearch.WordTrace tailWord_2024056 prefixEnd_2024056 230958577692630690064787 := by
  unfold tailWord_2024056
  simp only [CollatzResearch.WordTrace]
  refine ⟨36911693577599134044410011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49215591436798845392546681 36911693577599134044410011)
  ·
    refine ⟨55367540366398701066615017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36911693577599134044410011 55367540366398701066615017)
    ·
      refine ⟨41525655274799025799961263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55367540366398701066615017 41525655274799025799961263)
      ·
        refine ⟨62288482912198538699941895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41525655274799025799961263 62288482912198538699941895)
        ·
          refine ⟨93432724368297808049912843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62288482912198538699941895 93432724368297808049912843)
          ·
            refine ⟨140149086552446712074869265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93432724368297808049912843 140149086552446712074869265)
            ·
              refine ⟨105111814914335034056151949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140149086552446712074869265 105111814914335034056151949)
              ·
                refine ⟨39416930592875637771056981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105111814914335034056151949 39416930592875637771056981)
                ·
                  refine ⟨230958577692630690064787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39416930592875637771056981 230958577692630690064787)
                  ·
                    rfl

theorem cell22_2024056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_2024056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024056 prefixEnd_2024056 := by exact prefixLift 2024056
  have htrace : WordTrace (prefixWord ++ tailWord_2024056) baseStart_2024056 baseEnd_2024056 := by
    simpa [prefixWord, tailWord_2024056, baseEnd_2024056] using wordTrace_append hprefix tailTrace_2024056
  have hstable : (prefixWord ++ tailWord_2024056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024056).length < 2 ^ (prefixWord ++ tailWord_2024056).sum := by decide
  have hdescent : baseEnd_2024056 < baseStart_2024056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024066 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2024066 : Nat := 118140960795 + 2024066 * 2 ^ 59
def prefixEnd_2024066 : Nat := 4983230072969 + 3 ^ 40 * 2024066 * 2
def baseEnd_2024066 : Nat := 692879156282255377444331

theorem tailTrace_2024066 : CollatzResearch.WordTrace tailWord_2024066 prefixEnd_2024066 692879156282255377444331 := by
  unfold tailWord_2024066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18455937971290509949171013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49215834590108026531122701 18455937971290509949171013)
  ·
    refine ⟨3460488369616970615469565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18455937971290509949171013 3460488369616970615469565)
    ·
      refine ⟨1297683138606363980801087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3460488369616970615469565 1297683138606363980801087)
      ·
        refine ⟨1946524707909545971201631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1297683138606363980801087 1946524707909545971201631)
        ·
          refine ⟨2919787061864318956802447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946524707909545971201631 2919787061864318956802447)
          ·
            refine ⟨4379680592796478435203671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919787061864318956802447 4379680592796478435203671)
            ·
              refine ⟨6569520889194717652805507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379680592796478435203671 6569520889194717652805507)
              ·
                refine ⟨9854281333792076479208261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6569520889194717652805507 9854281333792076479208261)
                ·
                  refine ⟨1847677750086014339851549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9854281333792076479208261 1847677750086014339851549)
                  ·
                    refine ⟨692879156282255377444331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1847677750086014339851549 692879156282255377444331)
                    ·
                      rfl

theorem cell22_2024066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2024066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024066 prefixEnd_2024066 := by exact prefixLift 2024066
  have htrace : WordTrace (prefixWord ++ tailWord_2024066) baseStart_2024066 baseEnd_2024066 := by
    simpa [prefixWord, tailWord_2024066, baseEnd_2024066] using wordTrace_append hprefix tailTrace_2024066
  have hstable : (prefixWord ++ tailWord_2024066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024066).length < 2 ^ (prefixWord ++ tailWord_2024066).sum := by decide
  have hdescent : baseEnd_2024066 < baseStart_2024066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024088 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 2, 5]
def baseStart_2024088 : Nat := 118140960795 + 2024088 * 2 ^ 59
def prefixEnd_2024088 : Nat := 4983230072969 + 3 ^ 40 * 2024088 * 2
def baseEnd_2024088 : Nat := 692886687331854653394263

theorem tailTrace_2024088 : CollatzResearch.WordTrace tailWord_2024088 prefixEnd_2024088 692886687331854653394263 := by
  unfold tailWord_2024088
  simp only [CollatzResearch.WordTrace]
  refine ⟨36912277145541168776992459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49216369527388225035989945 36912277145541168776992459)
  ·
    refine ⟨55368415718311753165488689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36912277145541168776992459 55368415718311753165488689)
    ·
      refine ⟨41526311788733814874116517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55368415718311753165488689 41526311788733814874116517)
      ·
        refine ⟨7786183460387590288896847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41526311788733814874116517 7786183460387590288896847)
        ·
          refine ⟨11679275190581385433345271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7786183460387590288896847 11679275190581385433345271)
          ·
            refine ⟨17518912785872078150017907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11679275190581385433345271 17518912785872078150017907)
            ·
              refine ⟨26278369178808117225026861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17518912785872078150017907 26278369178808117225026861)
              ·
                refine ⟨9854388442053043959385073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26278369178808117225026861 9854388442053043959385073)
                ·
                  refine ⟨7390791331539782969538805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9854388442053043959385073 7390791331539782969538805)
                  ·
                    refine ⟨692886687331854653394263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7390791331539782969538805 692886687331854653394263)
                    ·
                      rfl

theorem cell22_2024088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_2024088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024088 prefixEnd_2024088 := by exact prefixLift 2024088
  have htrace : WordTrace (prefixWord ++ tailWord_2024088) baseStart_2024088 baseEnd_2024088 := by
    simpa [prefixWord, tailWord_2024088, baseEnd_2024088] using wordTrace_append hprefix tailTrace_2024088
  have hstable : (prefixWord ++ tailWord_2024088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024088).length < 2 ^ (prefixWord ++ tailWord_2024088).sum := by decide
  have hdescent : baseEnd_2024088 < baseStart_2024088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024141 : List Nat := [1, 6, 2, 1, 2, 2, 2, 1, 5]
def baseStart_2024141 : Nat := 118140960795 + 2024141 * 2 ^ 59
def prefixEnd_2024141 : Nat := 4983230072969 + 3 ^ 40 * 2024141 * 2
def baseEnd_2024141 : Nat := 230968276771660060606367

theorem tailTrace_2024141 : CollatzResearch.WordTrace tailWord_2024141 prefixEnd_2024141 230968276771660060606367 := by
  unfold tailWord_2024141
  simp only [CollatzResearch.WordTrace]
  refine ⟨73826487359890327605664277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49217658239926885070442851 73826487359890327605664277)
  ·
    refine ⟨3460616594994859106515513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73826487359890327605664277 3460616594994859106515513)
    ·
      refine ⟨2595462446246144329886635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3460616594994859106515513 2595462446246144329886635)
      ·
        refine ⟨3893193669369216494829953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2595462446246144329886635 3893193669369216494829953)
        ·
          refine ⟨2919895252026912371122465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3893193669369216494829953 2919895252026912371122465)
          ·
            refine ⟨2189921439020184278341849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2919895252026912371122465 2189921439020184278341849)
            ·
              refine ⟨1642441079265138208756387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2189921439020184278341849 1642441079265138208756387)
              ·
                refine ⟨2463661618897707313134581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642441079265138208756387 2463661618897707313134581)
                ·
                  refine ⟨230968276771660060606367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2463661618897707313134581 230968276771660060606367)
                  ·
                    rfl

theorem cell22_2024141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_2024141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024141 prefixEnd_2024141 := by exact prefixLift 2024141
  have htrace : WordTrace (prefixWord ++ tailWord_2024141) baseStart_2024141 baseEnd_2024141 := by
    simpa [prefixWord, tailWord_2024141, baseEnd_2024141] using wordTrace_append hprefix tailTrace_2024141
  have hstable : (prefixWord ++ tailWord_2024141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024141).length < 2 ^ (prefixWord ++ tailWord_2024141).sum := by decide
  have hdescent : baseEnd_2024141 < baseStart_2024141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024165 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_2024165 : Nat := 118140960795 + 2024165 * 2 ^ 59
def prefixEnd_2024165 : Nat := 4983230072969 + 3 ^ 40 * 2024165 * 2
def baseEnd_2024165 : Nat := 692913046005452119219027

theorem tailTrace_2024165 : CollatzResearch.WordTrace tailWord_2024165 prefixEnd_2024165 692913046005452119219027 := by
  unfold tailWord_2024165
  simp only [CollatzResearch.WordTrace]
  refine ⟨73827362711803379704537949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49218241807868919803025299 73827362711803379704537949)
  ·
    refine ⟨27685261016926267389201731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73827362711803379704537949 27685261016926267389201731)
    ·
      refine ⟨41527891525389401083802597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27685261016926267389201731 41527891525389401083802597)
      ·
        refine ⟨7786479661010512703212987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41527891525389401083802597 7786479661010512703212987)
        ·
          refine ⟨11679719491515769054819481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7786479661010512703212987 11679719491515769054819481)
          ·
            refine ⟨8759789618636826791114611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11679719491515769054819481 8759789618636826791114611)
            ·
              refine ⟨13139684427955240186671917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8759789618636826791114611 13139684427955240186671917)
              ·
                refine ⟨4927381660483215070001969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13139684427955240186671917 4927381660483215070001969)
                ·
                  refine ⟨3695536245362411302501477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4927381660483215070001969 3695536245362411302501477)
                  ·
                    refine ⟨692913046005452119219027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3695536245362411302501477 692913046005452119219027)
                    ·
                      rfl

theorem cell22_2024165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_2024165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024165 prefixEnd_2024165 := by exact prefixLift 2024165
  have htrace : WordTrace (prefixWord ++ tailWord_2024165) baseStart_2024165 baseEnd_2024165 := by
    simpa [prefixWord, tailWord_2024165, baseEnd_2024165] using wordTrace_append hprefix tailTrace_2024165
  have hstable : (prefixWord ++ tailWord_2024165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024165).length < 2 ^ (prefixWord ++ tailWord_2024165).sum := by decide
  have hdescent : baseEnd_2024165 < baseStart_2024165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024195 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 3, 3]
def baseStart_2024195 : Nat := 118140960795 + 2024195 * 2 ^ 59
def prefixEnd_2024195 : Nat := 4983230072969 + 3 ^ 40 * 2024195 * 2
def baseEnd_2024195 : Nat := 692923315618542040968935

theorem tailTrace_2024195 : CollatzResearch.WordTrace tailWord_2024195 prefixEnd_2024195 692923315618542040968935 := by
  unfold tailWord_2024195
  simp only [CollatzResearch.WordTrace]
  refine ⟨73828456901694694828130039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49218971267796463218753359 73828456901694694828130039)
  ·
    refine ⟨110742685352542042242195059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73828456901694694828130039 110742685352542042242195059)
    ·
      refine ⟨166114028028813063363292589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110742685352542042242195059 166114028028813063363292589)
      ·
        refine ⟨62292760510804898761234721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166114028028813063363292589 62292760510804898761234721)
        ·
          refine ⟨46719570383103674070926041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62292760510804898761234721 46719570383103674070926041)
          ·
            refine ⟨35039677787327755553194531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46719570383103674070926041 35039677787327755553194531)
            ·
              refine ⟨52559516680991633329791797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35039677787327755553194531 52559516680991633329791797)
              ·
                refine ⟨4927454688842965624667981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52559516680991633329791797 4927454688842965624667981)
                ·
                  refine ⟨1847795508316112109250493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4927454688842965624667981 1847795508316112109250493)
                  ·
                    refine ⟨692923315618542040968935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1847795508316112109250493 692923315618542040968935)
                    ·
                      rfl

theorem cell22_2024195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 3].length) (baseStart_2024195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024195 prefixEnd_2024195 := by exact prefixLift 2024195
  have htrace : WordTrace (prefixWord ++ tailWord_2024195) baseStart_2024195 baseEnd_2024195 := by
    simpa [prefixWord, tailWord_2024195, baseEnd_2024195] using wordTrace_append hprefix tailTrace_2024195
  have hstable : (prefixWord ++ tailWord_2024195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024195).length < 2 ^ (prefixWord ++ tailWord_2024195).sum := by decide
  have hdescent : baseEnd_2024195 < baseStart_2024195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024229 : List Nat := [1, 3, 1, 2, 3, 1, 4, 3, 1, 3]
def baseStart_2024229 : Nat := 118140960795 + 2024229 * 2 ^ 59
def prefixEnd_2024229 : Nat := 4983230072969 + 3 ^ 40 * 2024229 * 2
def baseEnd_2024229 : Nat := 692934954513377285618831

theorem tailTrace_2024229 : CollatzResearch.WordTrace tailWord_2024229 prefixEnd_2024229 692934954513377285618831 := by
  unfold tailWord_2024229
  simp only [CollatzResearch.WordTrace]
  refine ⟨73829696983571518634867741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49219797989047679089911827 73829696983571518634867741)
  ·
    refine ⟨27686136368839319488075403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73829696983571518634867741 27686136368839319488075403)
    ·
      refine ⟨41529204553258979232113105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27686136368839319488075403 41529204553258979232113105)
      ·
        refine ⟨31146903414944234424084829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41529204553258979232113105 31146903414944234424084829)
        ·
          refine ⟨11680088780604087909031811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31146903414944234424084829 11680088780604087909031811)
          ·
            refine ⟨17520133170906131863547717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11680088780604087909031811 17520133170906131863547717)
            ·
              refine ⟨3285024969544899724415197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17520133170906131863547717 3285024969544899724415197)
              ·
                refine ⟨1231884363579337396655699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3285024969544899724415197 1231884363579337396655699)
                ·
                  refine ⟨1847826545369006094983549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231884363579337396655699 1847826545369006094983549)
                  ·
                    refine ⟨692934954513377285618831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1847826545369006094983549 692934954513377285618831)
                    ·
                      rfl

theorem cell22_2024229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_2024229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024229 prefixEnd_2024229 := by exact prefixLift 2024229
  have htrace : WordTrace (prefixWord ++ tailWord_2024229) baseStart_2024229 baseEnd_2024229 := by
    simpa [prefixWord, tailWord_2024229, baseEnd_2024229] using wordTrace_append hprefix tailTrace_2024229
  have hstable : (prefixWord ++ tailWord_2024229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024229).length < 2 ^ (prefixWord ++ tailWord_2024229).sum := by decide
  have hdescent : baseEnd_2024229 < baseStart_2024229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024246 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_2024246 : Nat := 118140960795 + 2024246 * 2 ^ 59
def prefixEnd_2024246 : Nat := 4983230072969 + 3 ^ 40 * 2024246 * 2
def baseEnd_2024246 : Nat := 692940773960794907943779

theorem tailTrace_2024246 : CollatzResearch.WordTrace tailWord_2024246 prefixEnd_2024246 692940773960794907943779 := by
  unfold tailWord_2024246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4614394814031870658639787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49220211349673287025491061 4614394814031870658639787)
  ·
    refine ⟨6921592221047805987959681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4614394814031870658639787 6921592221047805987959681)
    ·
      refine ⟨5191194165785854490969761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6921592221047805987959681 5191194165785854490969761)
      ·
        refine ⟨3893395624339390868227321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5191194165785854490969761 3893395624339390868227321)
        ·
          refine ⟨2920046718254543151170491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3893395624339390868227321 2920046718254543151170491)
          ·
            refine ⟨4380070077381814726755737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920046718254543151170491 4380070077381814726755737)
            ·
              refine ⟨3285052558036361045066803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4380070077381814726755737 3285052558036361045066803)
              ·
                refine ⟨4927578837054541567600205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3285052558036361045066803 4927578837054541567600205)
                ·
                  refine ⟨1847842063895453087850077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4927578837054541567600205 1847842063895453087850077)
                  ·
                    refine ⟨692940773960794907943779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1847842063895453087850077 692940773960794907943779)
                    ·
                      rfl

theorem cell22_2024246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_2024246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024246 prefixEnd_2024246 := by exact prefixLift 2024246
  have htrace : WordTrace (prefixWord ++ tailWord_2024246) baseStart_2024246 baseEnd_2024246 := by
    simpa [prefixWord, tailWord_2024246, baseEnd_2024246] using wordTrace_append hprefix tailTrace_2024246
  have hstable : (prefixWord ++ tailWord_2024246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024246).length < 2 ^ (prefixWord ++ tailWord_2024246).sum := by decide
  have hdescent : baseEnd_2024246 < baseStart_2024246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024319 : List Nat := [1, 1, 2, 2, 1, 1, 8, 1, 2, 3]
def baseStart_2024319 : Nat := 118140960795 + 2024319 * 2 ^ 59
def prefixEnd_2024319 : Nat := 4983230072969 + 3 ^ 40 * 2024319 * 2
def baseEnd_2024319 : Nat := 692965763352647050868555

theorem tailTrace_2024319 : CollatzResearch.WordTrace tailWord_2024319 prefixEnd_2024319 692965763352647050868555 := by
  unfold tailWord_2024319
  simp only [CollatzResearch.WordTrace]
  refine ⟨73832979553245464005644011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49221986368830309337096007 73832979553245464005644011)
  ·
    refine ⟨110749469329868196008466017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73832979553245464005644011 110749469329868196008466017)
    ·
      refine ⟨83062101997401147006349513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110749469329868196008466017 83062101997401147006349513)
      ·
        refine ⟨62296576498050860254762135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83062101997401147006349513 62296576498050860254762135)
        ·
          refine ⟨93444864747076290382143203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62296576498050860254762135 93444864747076290382143203)
          ·
            refine ⟨140167297120614435573214805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93444864747076290382143203 140167297120614435573214805)
            ·
              refine ⟨1642585513132200416873611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 140167297120614435573214805 1642585513132200416873611)
              ·
                refine ⟨2463878269698300625310417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642585513132200416873611 2463878269698300625310417)
                ·
                  refine ⟨1847908702273725468982813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2463878269698300625310417 1847908702273725468982813)
                  ·
                    refine ⟨692965763352647050868555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1847908702273725468982813 692965763352647050868555)
                    ·
                      rfl

theorem cell22_2024319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 2, 3].length) (baseStart_2024319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024319 prefixEnd_2024319 := by exact prefixLift 2024319
  have htrace : WordTrace (prefixWord ++ tailWord_2024319) baseStart_2024319 baseEnd_2024319 := by
    simpa [prefixWord, tailWord_2024319, baseEnd_2024319] using wordTrace_append hprefix tailTrace_2024319
  have hstable : (prefixWord ++ tailWord_2024319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024319).length < 2 ^ (prefixWord ++ tailWord_2024319).sum := by decide
  have hdescent : baseEnd_2024319 < baseStart_2024319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024364 : List Nat := [2, 2, 1, 1, 1, 1, 2, 8, 1, 3]
def baseStart_2024364 : Nat := 118140960795 + 2024364 * 2 ^ 59
def prefixEnd_2024364 : Nat := 4983230072969 + 3 ^ 40 * 2024364 * 2
def baseEnd_2024364 : Nat := 692981167772281933493417

theorem tailTrace_2024364 : CollatzResearch.WordTrace tailWord_2024364 prefixEnd_2024364 692981167772281933493417 := by
  unfold tailWord_2024364
  simp only [CollatzResearch.WordTrace]
  refine ⟨36917310419041218345516073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49223080558721624460688097 36917310419041218345516073)
  ·
    refine ⟨27687982814280913759137055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36917310419041218345516073 27687982814280913759137055)
    ·
      refine ⟨41531974221421370638705583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27687982814280913759137055 41531974221421370638705583)
      ·
        refine ⟨62297961332132055958058375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41531974221421370638705583 62297961332132055958058375)
        ·
          refine ⟨93446941998198083937087563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62297961332132055958058375 93446941998198083937087563)
          ·
            refine ⟨140170412997297125905631345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93446941998198083937087563 140170412997297125905631345)
            ·
              refine ⟨105127809747972844429223509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140170412997297125905631345 105127809747972844429223509)
              ·
                refine ⟨1231966520484056770654963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 105127809747972844429223509 1231966520484056770654963)
                ·
                  refine ⟨1847949780726085155982445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231966520484056770654963 1847949780726085155982445)
                  ·
                    refine ⟨692981167772281933493417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1847949780726085155982445 692981167772281933493417)
                    ·
                      rfl

theorem cell22_2024364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_2024364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024364 prefixEnd_2024364 := by exact prefixLift 2024364
  have htrace : WordTrace (prefixWord ++ tailWord_2024364) baseStart_2024364 baseEnd_2024364 := by
    simpa [prefixWord, tailWord_2024364, baseEnd_2024364] using wordTrace_append hprefix tailTrace_2024364
  have hstable : (prefixWord ++ tailWord_2024364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024364).length < 2 ^ (prefixWord ++ tailWord_2024364).sum := by decide
  have hdescent : baseEnd_2024364 < baseStart_2024364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024375 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 1, 7]
def baseStart_2024375 : Nat := 118140960795 + 2024375 * 2 ^ 59
def prefixEnd_2024375 : Nat := 4983230072969 + 3 ^ 40 * 2024375 * 2
def baseEnd_2024375 : Nat := 692984933297081571468383

theorem tailTrace_2024375 : CollatzResearch.WordTrace tailWord_2024375 prefixEnd_2024375 692984933297081571468383 := by
  unfold tailWord_2024375
  simp only [CollatzResearch.WordTrace]
  refine ⟨73835022041042585569682579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49223348027361723713121719 73835022041042585569682579)
  ·
    refine ⟨110752533061563878354523869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73835022041042585569682579 110752533061563878354523869)
    ·
      refine ⟨41532199898086454382946451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110752533061563878354523869 41532199898086454382946451)
      ·
        refine ⟨62298299847129681574419677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41532199898086454382946451 62298299847129681574419677)
        ·
          refine ⟨23361862442673630590407379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62298299847129681574419677 23361862442673630590407379)
          ·
            refine ⟨35042793664010445885611069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23361862442673630590407379 35042793664010445885611069)
            ·
              refine ⟨13141047624003917207104151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35042793664010445885611069 13141047624003917207104151)
              ·
                refine ⟨19711571436005875810656227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13141047624003917207104151 19711571436005875810656227)
                ·
                  refine ⟨29567357154008813715984341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19711571436005875810656227 29567357154008813715984341)
                  ·
                    refine ⟨692984933297081571468383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29567357154008813715984341 692984933297081571468383)
                    ·
                      rfl

theorem cell22_2024375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_2024375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024375 prefixEnd_2024375 := by exact prefixLift 2024375
  have htrace : WordTrace (prefixWord ++ tailWord_2024375) baseStart_2024375 baseEnd_2024375 := by
    simpa [prefixWord, tailWord_2024375, baseEnd_2024375] using wordTrace_append hprefix tailTrace_2024375
  have hstable : (prefixWord ++ tailWord_2024375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024375).length < 2 ^ (prefixWord ++ tailWord_2024375).sum := by decide
  have hdescent : baseEnd_2024375 < baseStart_2024375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024377 : List Nat := [1, 2, 1, 4, 2, 2, 2, 3, 5]
def baseStart_2024377 : Nat := 118140960795 + 2024377 * 2 ^ 59
def prefixEnd_2024377 : Nat := 4983230072969 + 3 ^ 40 * 2024377 * 2
def baseEnd_2024377 : Nat := 230995205979318077639459

theorem tailTrace_2024377 : CollatzResearch.WordTrace tailWord_2024377 prefixEnd_2024377 230995205979318077639459 := by
  unfold tailWord_2024377
  simp only [CollatzResearch.WordTrace]
  refine ⟨73835094987035339911255385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49223396658023559940836923 73835094987035339911255385)
  ·
    refine ⟨55376321240276504933441539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73835094987035339911255385 55376321240276504933441539)
    ·
      refine ⟨83064481860414757400162309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55376321240276504933441539 83064481860414757400162309)
      ·
        refine ⟨15574590348827767012530433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83064481860414757400162309 15574590348827767012530433)
        ·
          refine ⟨11680942761620825259397825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15574590348827767012530433 11680942761620825259397825)
          ·
            refine ⟨8760707071215618944548369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11680942761620825259397825 8760707071215618944548369)
            ·
              refine ⟨6570530303411714208411277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8760707071215618944548369 6570530303411714208411277)
              ·
                refine ⟨2463948863779392828154229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6570530303411714208411277 2463948863779392828154229)
                ·
                  refine ⟨230995205979318077639459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2463948863779392828154229 230995205979318077639459)
                  ·
                    rfl

theorem cell22_2024377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 5].length) (baseStart_2024377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024377 prefixEnd_2024377 := by exact prefixLift 2024377
  have htrace : WordTrace (prefixWord ++ tailWord_2024377) baseStart_2024377 baseEnd_2024377 := by
    simpa [prefixWord, tailWord_2024377, baseEnd_2024377] using wordTrace_append hprefix tailTrace_2024377
  have hstable : (prefixWord ++ tailWord_2024377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024377).length < 2 ^ (prefixWord ++ tailWord_2024377).sum := by decide
  have hdescent : baseEnd_2024377 < baseStart_2024377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024456 : List Nat := [2, 1, 3, 2, 1, 5, 1, 3, 4]
def baseStart_2024456 : Nat := 118140960795 + 2024456 * 2 ^ 59
def prefixEnd_2024456 : Nat := 4983230072969 + 3 ^ 40 * 2024456 * 2
def baseEnd_2024456 : Nat := 231004220417474786731045

theorem tailTrace_2024456 : CollatzResearch.WordTrace tailWord_2024456 prefixEnd_2024456 231004220417474786731045 := by
  unfold tailWord_2024456
  simp only [CollatzResearch.WordTrace]
  refine ⟨36918988176874568201690611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49225317569166090935587481 36918988176874568201690611)
  ·
    refine ⟨55378482265311852302535917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36918988176874568201690611 55378482265311852302535917)
    ·
      refine ⟨20766930849491944613450969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55378482265311852302535917 20766930849491944613450969)
      ·
        refine ⟨15575198137118958460088227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20766930849491944613450969 15575198137118958460088227)
        ·
          refine ⟨23362797205678437690132341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15575198137118958460088227 23362797205678437690132341)
          ·
            refine ⟨2190262238032353533449907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23362797205678437690132341 2190262238032353533449907)
            ·
              refine ⟨3285393357048530300174861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190262238032353533449907 3285393357048530300174861)
              ·
                refine ⟨1232022508893198862565573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3285393357048530300174861 1232022508893198862565573)
                ·
                  refine ⟨231004220417474786731045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1232022508893198862565573 231004220417474786731045)
                  ·
                    rfl

theorem cell22_2024456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 4].length) (baseStart_2024456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024456 prefixEnd_2024456 := by exact prefixLift 2024456
  have htrace : WordTrace (prefixWord ++ tailWord_2024456) baseStart_2024456 baseEnd_2024456 := by
    simpa [prefixWord, tailWord_2024456, baseEnd_2024456] using wordTrace_append hprefix tailTrace_2024456
  have hstable : (prefixWord ++ tailWord_2024456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024456).length < 2 ^ (prefixWord ++ tailWord_2024456).sum := by decide
  have hdescent : baseEnd_2024456 < baseStart_2024456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024469 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_2024469 : Nat := 118140960795 + 2024469 * 2 ^ 59
def prefixEnd_2024469 : Nat := 4983230072969 + 3 ^ 40 * 2024469 * 2
def baseEnd_2024469 : Nat := 693017111418096659618095

theorem tailTrace_2024469 : CollatzResearch.WordTrace tailWord_2024469 prefixEnd_2024469 693017111418096659618095 := by
  unfold tailWord_2024469
  simp only [CollatzResearch.WordTrace]
  refine ⟨73838450502702039623604461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49225633668468026415736307 73838450502702039623604461)
  ·
    refine ⟨27689418938513264858851673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73838450502702039623604461 27689418938513264858851673)
    ·
      refine ⟨20767064203884948644138755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27689418938513264858851673 20767064203884948644138755)
      ·
        refine ⟨31150596305827422966208133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20767064203884948644138755 31150596305827422966208133)
        ·
          refine ⟨5840736807342641806164025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31150596305827422966208133 5840736807342641806164025)
          ·
            refine ⟨4380552605506981354623019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5840736807342641806164025 4380552605506981354623019)
            ·
              refine ⟨6570828908260472031934529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4380552605506981354623019 6570828908260472031934529)
              ·
                refine ⟨4928121681195354023950897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6570828908260472031934529 4928121681195354023950897)
                ·
                  refine ⟨3696091260896515517963173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4928121681195354023950897 3696091260896515517963173)
                  ·
                    refine ⟨693017111418096659618095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3696091260896515517963173 693017111418096659618095)
                    ·
                      rfl

theorem cell22_2024469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_2024469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024469 prefixEnd_2024469 := by exact prefixLift 2024469
  have htrace : WordTrace (prefixWord ++ tailWord_2024469) baseStart_2024469 baseEnd_2024469 := by
    simpa [prefixWord, tailWord_2024469, baseEnd_2024469] using wordTrace_append hprefix tailTrace_2024469
  have hstable : (prefixWord ++ tailWord_2024469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024469).length < 2 ^ (prefixWord ++ tailWord_2024469).sum := by decide
  have hdescent : baseEnd_2024469 < baseStart_2024469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024484 : List Nat := [2, 3, 1, 4, 1, 2, 2, 7]
def baseStart_2024484 : Nat := 118140960795 + 2024484 * 2 ^ 59
def prefixEnd_2024484 : Nat := 4983230072969 + 3 ^ 40 * 2024484 * 2
def baseEnd_2024484 : Nat := 77002471802737957832561

theorem tailTrace_2024484 : CollatzResearch.WordTrace tailWord_2024484 prefixEnd_2024484 77002471802737957832561 := by
  unfold tailWord_2024484
  simp only [CollatzResearch.WordTrace]
  refine ⟨36919498798823848592700253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49225998398431798123600337 36919498798823848592700253)
  ·
    refine ⟨13844812049558943222262595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36919498798823848592700253 13844812049558943222262595)
    ·
      refine ⟨20767218074338414833393893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13844812049558943222262595 20767218074338414833393893)
      ·
        refine ⟨3893853388938452781261355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20767218074338414833393893 3893853388938452781261355)
        ·
          refine ⟨5840780083407679171892033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893853388938452781261355 5840780083407679171892033)
          ·
            refine ⟨4380585062555759378919025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5840780083407679171892033 4380585062555759378919025)
            ·
              refine ⟨3285438796916819534189269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4380585062555759378919025 3285438796916819534189269)
              ·
                refine ⟨77002471802737957832561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3285438796916819534189269 77002471802737957832561)
                ·
                  rfl

theorem cell22_2024484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 7].length) (baseStart_2024484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024484 prefixEnd_2024484 := by exact prefixLift 2024484
  have htrace : WordTrace (prefixWord ++ tailWord_2024484) baseStart_2024484 baseEnd_2024484 := by
    simpa [prefixWord, tailWord_2024484, baseEnd_2024484] using wordTrace_append hprefix tailTrace_2024484
  have hstable : (prefixWord ++ tailWord_2024484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024484).length < 2 ^ (prefixWord ++ tailWord_2024484).sum := by decide
  have hdescent : baseEnd_2024484 < baseStart_2024484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024546 : List Nat := [3, 3, 2, 2, 1, 1, 2, 3, 5]
def baseStart_2024546 : Nat := 118140960795 + 2024546 * 2 ^ 59
def prefixEnd_2024546 : Nat := 4983230072969 + 3 ^ 40 * 2024546 * 2
def baseEnd_2024546 : Nat := 231014490030564708480953

theorem tailTrace_2024546 : CollatzResearch.WordTrace tailWord_2024546 prefixEnd_2024546 231014490030564708480953 := by
  unfold tailWord_2024546
  simp only [CollatzResearch.WordTrace]
  refine ⟨18460314730855770443539373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49227505948948721182771661 18460314730855770443539373)
  ·
    refine ⟨6922618024070913916327265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18460314730855770443539373 6922618024070913916327265)
    ·
      refine ⟨5191963518053185437245449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6922618024070913916327265 5191963518053185437245449)
      ·
        refine ⟨3893972638539889077934087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5191963518053185437245449 3893972638539889077934087)
        ·
          refine ⟨5840958957809833616901131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893972638539889077934087 5840958957809833616901131)
          ·
            refine ⟨8761438436714750425351697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5840958957809833616901131 8761438436714750425351697)
            ·
              refine ⟨6571078827536062819013773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8761438436714750425351697 6571078827536062819013773)
              ·
                refine ⟨2464154560326023557130165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6571078827536062819013773 2464154560326023557130165)
                ·
                  refine ⟨231014490030564708480953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2464154560326023557130165 231014490030564708480953)
                  ·
                    rfl

theorem cell22_2024546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_2024546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024546 prefixEnd_2024546 := by exact prefixLift 2024546
  have htrace : WordTrace (prefixWord ++ tailWord_2024546) baseStart_2024546 baseEnd_2024546 := by
    simpa [prefixWord, tailWord_2024546, baseEnd_2024546] using wordTrace_append hprefix tailTrace_2024546
  have hstable : (prefixWord ++ tailWord_2024546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024546).length < 2 ^ (prefixWord ++ tailWord_2024546).sum := by decide
  have hdescent : baseEnd_2024546 < baseStart_2024546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024559 : List Nat := [1, 1, 2, 1, 3, 3, 2, 4, 1, 4]
def baseStart_2024559 : Nat := 118140960795 + 2024559 * 2 ^ 59
def prefixEnd_2024559 : Nat := 4983230072969 + 3 ^ 40 * 2024559 * 2
def baseEnd_2024559 : Nat := 693047920257366424867819

theorem tailTrace_2024559 : CollatzResearch.WordTrace tailWord_2024559 prefixEnd_2024559 693047920257366424867819 := by
  unfold tailWord_2024559
  simp only [CollatzResearch.WordTrace]
  refine ⟨73841733072375984994380731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49227822048250656662920487 73841733072375984994380731)
  ·
    refine ⟨110762599608563977491571097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73841733072375984994380731 110762599608563977491571097)
    ·
      refine ⟨83071949706422983118678323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110762599608563977491571097 83071949706422983118678323)
      ·
        refine ⟨124607924559634474678017485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83071949706422983118678323 124607924559634474678017485)
        ·
          refine ⟨46727971709862928004256557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124607924559634474678017485 46727971709862928004256557)
          ·
            refine ⟨17522989391198598001596209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46727971709862928004256557 17522989391198598001596209)
            ·
              refine ⟨13142242043398948501197157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17522989391198598001596209 13142242043398948501197157)
              ·
                refine ⟨2464170383137302843974467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13142242043398948501197157 2464170383137302843974467)
                ·
                  refine ⟨3696255574705954265961701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464170383137302843974467 3696255574705954265961701)
                  ·
                    refine ⟨693047920257366424867819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3696255574705954265961701 693047920257366424867819)
                    ·
                      rfl

theorem cell22_2024559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_2024559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024559 prefixEnd_2024559 := by exact prefixLift 2024559
  have htrace : WordTrace (prefixWord ++ tailWord_2024559) baseStart_2024559 baseEnd_2024559 := by
    simpa [prefixWord, tailWord_2024559, baseEnd_2024559] using wordTrace_append hprefix tailTrace_2024559
  have hstable : (prefixWord ++ tailWord_2024559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024559).length < 2 ^ (prefixWord ++ tailWord_2024559).sum := by decide
  have hdescent : baseEnd_2024559 < baseStart_2024559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024576 : List Nat := [2, 1, 1, 2, 1, 3, 6, 1, 1, 4]
def baseStart_2024576 : Nat := 118140960795 + 2024576 * 2 ^ 59
def prefixEnd_2024576 : Nat := 4983230072969 + 3 ^ 40 * 2024576 * 2
def baseEnd_2024576 : Nat := 693053739704784047192767

theorem tailTrace_2024576 : CollatzResearch.WordTrace tailWord_2024576 prefixEnd_2024576 693053739704784047192767 := by
  unfold tailWord_2024576
  simp only [CollatzResearch.WordTrace]
  refine ⟨36921176556657198448874791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49228235408876264598499721 36921176556657198448874791)
  ·
    refine ⟨55381764834985797673312187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36921176556657198448874791 55381764834985797673312187)
    ·
      refine ⟨83072647252478696509968281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55381764834985797673312187 83072647252478696509968281)
      ·
        refine ⟨62304485439359022382476211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83072647252478696509968281 62304485439359022382476211)
        ·
          refine ⟨93456728159038533573714317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62304485439359022382476211 93456728159038533573714317)
          ·
            refine ⟨35046273059639450090142869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93456728159038533573714317 35046273059639450090142869)
            ·
              refine ⟨1642794049670599222975447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35046273059639450090142869 1642794049670599222975447)
              ·
                refine ⟨2464191074505898834463171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642794049670599222975447 2464191074505898834463171)
                ·
                  refine ⟨3696286611758848251694757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464191074505898834463171 3696286611758848251694757)
                  ·
                    refine ⟨693053739704784047192767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3696286611758848251694757 693053739704784047192767)
                    ·
                      rfl

theorem cell22_2024576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 1, 4].length) (baseStart_2024576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024576 prefixEnd_2024576 := by exact prefixLift 2024576
  have htrace : WordTrace (prefixWord ++ tailWord_2024576) baseStart_2024576 baseEnd_2024576 := by
    simpa [prefixWord, tailWord_2024576, baseEnd_2024576] using wordTrace_append hprefix tailTrace_2024576
  have hstable : (prefixWord ++ tailWord_2024576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024576).length < 2 ^ (prefixWord ++ tailWord_2024576).sum := by decide
  have hdescent : baseEnd_2024576 < baseStart_2024576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024604 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_2024604 : Nat := 118140960795 + 2024604 * 2 ^ 59
def prefixEnd_2024604 : Nat := 4983230072969 + 3 ^ 40 * 2024604 * 2
def baseEnd_2024604 : Nat := 693063324677001307492681

theorem tailTrace_2024604 : CollatzResearch.WordTrace tailWord_2024604 prefixEnd_2024604 693063324677001307492681 := by
  unfold tailWord_2024604
  simp only [CollatzResearch.WordTrace]
  refine ⟨36921687178606478839884433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49228916238141971786512577 36921687178606478839884433)
  ·
    refine ⟨27691265383954859129913325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36921687178606478839884433 27691265383954859129913325)
    ·
      refine ⟨10384224518983072173717497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27691265383954859129913325 10384224518983072173717497)
      ·
        refine ⟨7788168389237304130288123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10384224518983072173717497 7788168389237304130288123)
        ·
          refine ⟨11682252583855956195432185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7788168389237304130288123 11682252583855956195432185)
          ·
            refine ⟨8761689437891967146574139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11682252583855956195432185 8761689437891967146574139)
            ·
              refine ⟨13142534156837950719861209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8761689437891967146574139 13142534156837950719861209)
              ·
                refine ⟨9856900617628463039895907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13142534156837950719861209 9856900617628463039895907)
                ·
                  refine ⟨14785350926442694559843861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9856900617628463039895907 14785350926442694559843861)
                  ·
                    refine ⟨693063324677001307492681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14785350926442694559843861 693063324677001307492681)
                    ·
                      rfl

theorem cell22_2024604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_2024604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024604 prefixEnd_2024604 := by exact prefixLift 2024604
  have htrace : WordTrace (prefixWord ++ tailWord_2024604) baseStart_2024604 baseEnd_2024604 := by
    simpa [prefixWord, tailWord_2024604, baseEnd_2024604] using wordTrace_append hprefix tailTrace_2024604
  have hstable : (prefixWord ++ tailWord_2024604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024604).length < 2 ^ (prefixWord ++ tailWord_2024604).sum := by decide
  have hdescent : baseEnd_2024604 < baseStart_2024604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024642 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2024642 : Nat := 118140960795 + 2024642 * 2 ^ 59
def prefixEnd_2024642 : Nat := 4983230072969 + 3 ^ 40 * 2024642 * 2
def baseEnd_2024642 : Nat := 231025444284527291680855

theorem tailTrace_2024642 : CollatzResearch.WordTrace tailWord_2024642 prefixEnd_2024642 231025444284527291680855 := by
  unfold tailWord_2024642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18461190082768822542413045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49229840220716860113101453 18461190082768822542413045)
  ·
    refine ⟨1730736570259577113351223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18461190082768822542413045 1730736570259577113351223)
    ·
      refine ⟨2596104855389365670026835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1730736570259577113351223 2596104855389365670026835)
      ·
        refine ⟨3894157283084048505040253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2596104855389365670026835 3894157283084048505040253)
        ·
          refine ⟨1460308981156518189390095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3894157283084048505040253 1460308981156518189390095)
          ·
            refine ⟨2190463471734777284085143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460308981156518189390095 2190463471734777284085143)
            ·
              refine ⟨3285695207602165926127715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190463471734777284085143 3285695207602165926127715)
              ·
                refine ⟨4928542811403248889191573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3285695207602165926127715 4928542811403248889191573)
                ·
                  refine ⟨231025444284527291680855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4928542811403248889191573 231025444284527291680855)
                  ·
                    rfl

theorem cell22_2024642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2024642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024642 prefixEnd_2024642 := by exact prefixLift 2024642
  have htrace : WordTrace (prefixWord ++ tailWord_2024642) baseStart_2024642 baseEnd_2024642 := by
    simpa [prefixWord, tailWord_2024642, baseEnd_2024642] using wordTrace_append hprefix tailTrace_2024642
  have hstable : (prefixWord ++ tailWord_2024642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024642).length < 2 ^ (prefixWord ++ tailWord_2024642).sum := by decide
  have hdescent : baseEnd_2024642 < baseStart_2024642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024702 : List Nat := [4, 2, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_2024702 : Nat := 118140960795 + 2024702 * 2 ^ 59
def prefixEnd_2024702 : Nat := 4983230072969 + 3 ^ 40 * 2024702 * 2
def baseEnd_2024702 : Nat := 693096872079761718542381

theorem tailTrace_2024702 : CollatzResearch.WordTrace tailWord_2024702 prefixEnd_2024702 693096872079761718542381 := by
  unfold tailWord_2024702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9230868588857240052104545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49231299140571946944557573 9230868588857240052104545)
  ·
    refine ⟨6923151441642930039078409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9230868588857240052104545 6923151441642930039078409)
    ·
      refine ⟨5192363581232197529308807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6923151441642930039078409 5192363581232197529308807)
      ·
        refine ⟨7788545371848296293963211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5192363581232197529308807 7788545371848296293963211)
        ·
          refine ⟨11682818057772444440944817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7788545371848296293963211 11682818057772444440944817)
          ·
            refine ⟨8762113543329333330708613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11682818057772444440944817 8762113543329333330708613)
            ·
              refine ⟨1642896289374249999507865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8762113543329333330708613 1642896289374249999507865)
              ·
                refine ⟨1232172217030687499630899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1642896289374249999507865 1232172217030687499630899)
                ·
                  refine ⟨1848258325546031249446349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232172217030687499630899 1848258325546031249446349)
                  ·
                    refine ⟨693096872079761718542381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1848258325546031249446349 693096872079761718542381)
                    ·
                      rfl

theorem cell22_2024702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_2024702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024702 prefixEnd_2024702 := by exact prefixLift 2024702
  have htrace : WordTrace (prefixWord ++ tailWord_2024702) baseStart_2024702 baseEnd_2024702 := by
    simpa [prefixWord, tailWord_2024702, baseEnd_2024702] using wordTrace_append hprefix tailTrace_2024702
  have hstable : (prefixWord ++ tailWord_2024702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024702).length < 2 ^ (prefixWord ++ tailWord_2024702).sum := by decide
  have hdescent : baseEnd_2024702 < baseStart_2024702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024709 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 6]
def baseStart_2024709 : Nat := 118140960795 + 2024709 * 2 ^ 59
def prefixEnd_2024709 : Nat := 4983230072969 + 3 ^ 40 * 2024709 * 2
def baseEnd_2024709 : Nat := 231033089440938677872453

theorem tailTrace_2024709 : CollatzResearch.WordTrace tailWord_2024709 prefixEnd_2024709 231033089440938677872453 := by
  unfold tailWord_2024709
  simp only [CollatzResearch.WordTrace]
  refine ⟨73847204021832560612341181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49231469347888373741560787 73847204021832560612341181)
  ·
    refine ⟨27692701508187210229627943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73847204021832560612341181 27692701508187210229627943)
    ·
      refine ⟨41539052262280815344441915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27692701508187210229627943 41539052262280815344441915)
      ·
        refine ⟨62308578393421223016662873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41539052262280815344441915 62308578393421223016662873)
        ·
          refine ⟨46731433795065917262497155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62308578393421223016662873 46731433795065917262497155)
          ·
            refine ⟨70097150692598875893745733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46731433795065917262497155 70097150692598875893745733)
            ·
              refine ⟨13143215754862289230077325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70097150692598875893745733 13143215754862289230077325)
              ·
                refine ⟨4928705908073358461278997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13143215754862289230077325 4928705908073358461278997)
                ·
                  refine ⟨231033089440938677872453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4928705908073358461278997 231033089440938677872453)
                  ·
                    rfl

theorem cell22_2024709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_2024709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024709 prefixEnd_2024709 := by exact prefixLift 2024709
  have htrace : WordTrace (prefixWord ++ tailWord_2024709) baseStart_2024709 baseEnd_2024709 := by
    simpa [prefixWord, tailWord_2024709, baseEnd_2024709] using wordTrace_append hprefix tailTrace_2024709
  have hstable : (prefixWord ++ tailWord_2024709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024709).length < 2 ^ (prefixWord ++ tailWord_2024709).sum := by decide
  have hdescent : baseEnd_2024709 < baseStart_2024709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024741 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_2024741 : Nat := 118140960795 + 2024741 * 2 ^ 59
def prefixEnd_2024741 : Nat := 4983230072969 + 3 ^ 40 * 2024741 * 2
def baseEnd_2024741 : Nat := 693110222576778616817261

theorem tailTrace_2024741 : CollatzResearch.WordTrace tailWord_2024741 prefixEnd_2024741 693110222576778616817261 := by
  unfold tailWord_2024741
  simp only [CollatzResearch.WordTrace]
  refine ⟨73848371157716630077506077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49232247438477753385004051 73848371157716630077506077)
  ·
    refine ⟨27693139184143736279064779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73848371157716630077506077 27693139184143736279064779)
    ·
      refine ⟨41539708776215604418597169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27693139184143736279064779 41539708776215604418597169)
      ·
        refine ⟨31154781582161703313947877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41539708776215604418597169 31154781582161703313947877)
        ·
          refine ⟨5841521546655319371365227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31154781582161703313947877 5841521546655319371365227)
          ·
            refine ⟨8762282319982979057047841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841521546655319371365227 8762282319982979057047841)
            ·
              refine ⟨6571711739987234292785881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8762282319982979057047841 6571711739987234292785881)
              ·
                refine ⟨4928783804990425719589411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6571711739987234292785881 4928783804990425719589411)
                ·
                  refine ⟨7393175707485638579384117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4928783804990425719589411 7393175707485638579384117)
                  ·
                    refine ⟨693110222576778616817261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7393175707485638579384117 693110222576778616817261)
                    ·
                      rfl

theorem cell22_2024741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_2024741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024741 prefixEnd_2024741 := by exact prefixLift 2024741
  have htrace : WordTrace (prefixWord ++ tailWord_2024741) baseStart_2024741 baseEnd_2024741 := by
    simpa [prefixWord, tailWord_2024741, baseEnd_2024741] using wordTrace_append hprefix tailTrace_2024741
  have hstable : (prefixWord ++ tailWord_2024741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024741).length < 2 ^ (prefixWord ++ tailWord_2024741).sum := by decide
  have hdescent : baseEnd_2024741 < baseStart_2024741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024775 : List Nat := [1, 1, 4, 1, 2, 4, 3, 1, 2, 3]
def baseStart_2024775 : Nat := 118140960795 + 2024775 * 2 ^ 59
def prefixEnd_2024775 : Nat := 4983230072969 + 3 ^ 40 * 2024775 * 2
def baseEnd_2024775 : Nat := 693121861471613861467157

theorem tailTrace_2024775 : CollatzResearch.WordTrace tailWord_2024775 prefixEnd_2024775 693121861471613861467157 := by
  unfold tailWord_2024775
  simp only [CollatzResearch.WordTrace]
  refine ⟨73849611239593453884243779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49233074159728969256162519 73849611239593453884243779)
  ·
    refine ⟨110774416859390180826365669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73849611239593453884243779 110774416859390180826365669)
    ·
      refine ⟨20770203161135658904943563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110774416859390180826365669 20770203161135658904943563)
      ·
        refine ⟨31155304741703488357415345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20770203161135658904943563 31155304741703488357415345)
        ·
          refine ⟨23366478556277616268061509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31155304741703488357415345 23366478556277616268061509)
          ·
            refine ⟨4381214729302053050261533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23366478556277616268061509 4381214729302053050261533)
            ·
              refine ⟨1642955523488269893848075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4381214729302053050261533 1642955523488269893848075)
              ·
                refine ⟨2464433285232404840772113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642955523488269893848075 2464433285232404840772113)
                ·
                  refine ⟨1848324963924303630579085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2464433285232404840772113 1848324963924303630579085)
                  ·
                    refine ⟨693121861471613861467157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1848324963924303630579085 693121861471613861467157)
                    ·
                      rfl

theorem cell22_2024775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_2024775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024775 prefixEnd_2024775 := by exact prefixLift 2024775
  have htrace : WordTrace (prefixWord ++ tailWord_2024775) baseStart_2024775 baseEnd_2024775 := by
    simpa [prefixWord, tailWord_2024775, baseEnd_2024775] using wordTrace_append hprefix tailTrace_2024775
  have hstable : (prefixWord ++ tailWord_2024775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024775).length < 2 ^ (prefixWord ++ tailWord_2024775).sum := by decide
  have hdescent : baseEnd_2024775 < baseStart_2024775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024816 : List Nat := [2, 1, 1, 1, 4, 2, 2, 4, 5]
def baseStart_2024816 : Nat := 118140960795 + 2024816 * 2 ^ 59
def prefixEnd_2024816 : Nat := 4983230072969 + 3 ^ 40 * 2024816 * 2
def baseEnd_2024816 : Nat := 231045298869834473730677

theorem tailTrace_2024816 : CollatzResearch.WordTrace tailWord_2024816 prefixEnd_2024816 231045298869834473730677 := by
  unfold tailWord_2024816
  simp only [CollatzResearch.WordTrace]
  refine ⟨36925553316222458943243151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49234071088296611924324201 36925553316222458943243151)
  ·
    refine ⟨55388329974333688414864727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36925553316222458943243151 55388329974333688414864727)
    ·
      refine ⟨83082494961500532622297091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55388329974333688414864727 83082494961500532622297091)
      ·
        refine ⟨124623742442250798933445637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83082494961500532622297091 124623742442250798933445637)
        ·
          refine ⟨23366951707922024800021057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124623742442250798933445637 23366951707922024800021057)
          ·
            refine ⟨17525213780941518600015793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23366951707922024800021057 17525213780941518600015793)
            ·
              refine ⟨13143910335706138950011845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17525213780941518600015793 13143910335706138950011845)
              ·
                refine ⟨2464483187944901053127221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13143910335706138950011845 2464483187944901053127221)
                ·
                  refine ⟨231045298869834473730677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2464483187944901053127221 231045298869834473730677)
                  ·
                    rfl

theorem cell22_2024816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 5].length) (baseStart_2024816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024816 prefixEnd_2024816 := by exact prefixLift 2024816
  have htrace : WordTrace (prefixWord ++ tailWord_2024816) baseStart_2024816 baseEnd_2024816 := by
    simpa [prefixWord, tailWord_2024816, baseEnd_2024816] using wordTrace_append hprefix tailTrace_2024816
  have hstable : (prefixWord ++ tailWord_2024816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024816).length < 2 ^ (prefixWord ++ tailWord_2024816).sum := by decide
  have hdescent : baseEnd_2024816 < baseStart_2024816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024893 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_2024893 : Nat := 118140960795 + 2024893 * 2 ^ 59
def prefixEnd_2024893 : Nat := 4983230072969 + 3 ^ 40 * 2024893 * 2
def baseEnd_2024893 : Nat := 693162255283100887016795

theorem tailTrace_2024893 : CollatzResearch.WordTrace tailWord_2024893 prefixEnd_2024893 693162255283100887016795 := by
  unfold tailWord_2024893
  simp only [CollatzResearch.WordTrace]
  refine ⟨73853915053165960037039333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49235943368777306691359555 73853915053165960037039333)
  ·
    refine ⟨13847609072468617506944875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73853915053165960037039333 13847609072468617506944875)
    ·
      refine ⟨20771413608702926260417313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13847609072468617506944875 20771413608702926260417313)
      ·
        refine ⟨15578560206527194695312985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20771413608702926260417313 15578560206527194695312985)
        ·
          refine ⟨11683920154895396021484739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15578560206527194695312985 11683920154895396021484739)
          ·
            refine ⟨17525880232343094032227109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11683920154895396021484739 17525880232343094032227109)
            ·
              refine ⟨3286102543564330131042583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17525880232343094032227109 3286102543564330131042583)
              ·
                refine ⟨4929153815346495196563875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286102543564330131042583 4929153815346495196563875)
                ·
                  refine ⟨7393730723019742794845813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929153815346495196563875 7393730723019742794845813)
                  ·
                    refine ⟨693162255283100887016795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7393730723019742794845813 693162255283100887016795)
                    ·
                      rfl

theorem cell22_2024893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_2024893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024893 prefixEnd_2024893 := by exact prefixLift 2024893
  have htrace : WordTrace (prefixWord ++ tailWord_2024893) baseStart_2024893 baseEnd_2024893 := by
    simpa [prefixWord, tailWord_2024893, baseEnd_2024893] using wordTrace_append hprefix tailTrace_2024893
  have hstable : (prefixWord ++ tailWord_2024893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024893).length < 2 ^ (prefixWord ++ tailWord_2024893).sum := by decide
  have hdescent : baseEnd_2024893 < baseStart_2024893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024908 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_2024908 : Nat := 118140960795 + 2024908 * 2 ^ 59
def prefixEnd_2024908 : Nat := 4983230072969 + 3 ^ 40 * 2024908 * 2
def baseEnd_2024908 : Nat := 693167390089645847891749

theorem tailTrace_2024908 : CollatzResearch.WordTrace tailWord_2024908 prefixEnd_2024908 693167390089645847891749 := by
  unfold tailWord_2024908
  simp only [CollatzResearch.WordTrace]
  refine ⟨36927231074055808799417689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49236308098741078399223585 36927231074055808799417689)
  ·
    refine ⟨27695423305541856599563267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36927231074055808799417689 27695423305541856599563267)
    ·
      refine ⟨41543134958312784899344901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27695423305541856599563267 41543134958312784899344901)
      ·
        refine ⟨7789337804683647168627169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41543134958312784899344901 7789337804683647168627169)
        ·
          refine ⟨5842003353512735376470377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7789337804683647168627169 5842003353512735376470377)
          ·
            refine ⟨4381502515134551532352783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5842003353512735376470377 4381502515134551532352783)
            ·
              refine ⟨6572253772701827298529175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4381502515134551532352783 6572253772701827298529175)
              ·
                refine ⟨9858380659052740947793763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6572253772701827298529175 9858380659052740947793763)
                ·
                  refine ⟨14787570988579111421690645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9858380659052740947793763 14787570988579111421690645)
                  ·
                    refine ⟨693167390089645847891749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14787570988579111421690645 693167390089645847891749)
                    ·
                      rfl

theorem cell22_2024908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_2024908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024908 prefixEnd_2024908 := by exact prefixLift 2024908
  have htrace : WordTrace (prefixWord ++ tailWord_2024908) baseStart_2024908 baseEnd_2024908 := by
    simpa [prefixWord, tailWord_2024908, baseEnd_2024908] using wordTrace_append hprefix tailTrace_2024908
  have hstable : (prefixWord ++ tailWord_2024908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024908).length < 2 ^ (prefixWord ++ tailWord_2024908).sum := by decide
  have hdescent : baseEnd_2024908 < baseStart_2024908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024989 : List Nat := [1, 4, 2, 2, 1, 1, 5, 2, 1, 3]
def baseStart_2024989 : Nat := 118140960795 + 2024989 * 2 ^ 59
def prefixEnd_2024989 : Nat := 4983230072969 + 3 ^ 40 * 2024989 * 2
def baseEnd_2024989 : Nat := 693195118044988636616501

theorem tailTrace_2024989 : CollatzResearch.WordTrace tailWord_2024989 prefixEnd_2024989 693195118044988636616501 := by
  unfold tailWord_2024989
  simp only [CollatzResearch.WordTrace]
  refine ⟨73857416460818168432534021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49238277640545445621689347 73857416460818168432534021)
  ·
    refine ⟨13848265586403406581100129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73857416460818168432534021 13848265586403406581100129)
    ·
      refine ⟨10386199189802554935825097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13848265586403406581100129 10386199189802554935825097)
      ·
        refine ⟨7789649392351916201868823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10386199189802554935825097 7789649392351916201868823)
        ·
          refine ⟨11684474088527874302803235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7789649392351916201868823 11684474088527874302803235)
          ·
            refine ⟨17526711132791811454204853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11684474088527874302803235 17526711132791811454204853)
            ·
              refine ⟨1643129168699232323831705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17526711132791811454204853 1643129168699232323831705)
              ·
                refine ⟨1232346876524424242873779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643129168699232323831705 1232346876524424242873779)
                ·
                  refine ⟨1848520314786636364310669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232346876524424242873779 1848520314786636364310669)
                  ·
                    refine ⟨693195118044988636616501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1848520314786636364310669 693195118044988636616501)
                    ·
                      rfl

theorem cell22_2024989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_2024989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2024989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2024989 prefixEnd_2024989 := by exact prefixLift 2024989
  have htrace : WordTrace (prefixWord ++ tailWord_2024989) baseStart_2024989 baseEnd_2024989 := by
    simpa [prefixWord, tailWord_2024989, baseEnd_2024989] using wordTrace_append hprefix tailTrace_2024989
  have hstable : (prefixWord ++ tailWord_2024989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024989).length < 2 ^ (prefixWord ++ tailWord_2024989).sum := by decide
  have hdescent : baseEnd_2024989 < baseStart_2024989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025015 : List Nat := [1, 1, 3, 1, 2, 4, 3, 2, 1, 4]
def baseStart_2025015 : Nat := 118140960795 + 2025015 * 2 ^ 59
def prefixEnd_2025015 : Nat := 4983230072969 + 3 ^ 40 * 2025015 * 2
def baseEnd_2025015 : Nat := 693204018376333235466421

theorem tailTrace_2025015 : CollatzResearch.WordTrace tailWord_2025015 prefixEnd_2025015 693204018376333235466421 := by
  unfold tailWord_2025015
  simp only [CollatzResearch.WordTrace]
  refine ⟨73858364758723974872980499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49238909839149316581986999 73858364758723974872980499)
  ·
    refine ⟨110787547138085962309470749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73858364758723974872980499 110787547138085962309470749)
    ·
      refine ⟨41545330176782235866051531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110787547138085962309470749 41545330176782235866051531)
      ·
        refine ⟨62317995265173353799077297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41545330176782235866051531 62317995265173353799077297)
        ·
          refine ⟨46738496448880015349307973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62317995265173353799077297 46738496448880015349307973)
          ·
            refine ⟨8763468084165002877995245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46738496448880015349307973 8763468084165002877995245)
            ·
              refine ⟨3286300531561876079248217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8763468084165002877995245 3286300531561876079248217)
              ·
                refine ⟨2464725398671407059436163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3286300531561876079248217 2464725398671407059436163)
                ·
                  refine ⟨3697088098007110589154245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464725398671407059436163 3697088098007110589154245)
                  ·
                    refine ⟨693204018376333235466421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3697088098007110589154245 693204018376333235466421)
                    ·
                      rfl

theorem cell22_2025015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_2025015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025015 prefixEnd_2025015 := by exact prefixLift 2025015
  have htrace : WordTrace (prefixWord ++ tailWord_2025015) baseStart_2025015 baseEnd_2025015 := by
    simpa [prefixWord, tailWord_2025015, baseEnd_2025015] using wordTrace_append hprefix tailTrace_2025015
  have hstable : (prefixWord ++ tailWord_2025015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025015).length < 2 ^ (prefixWord ++ tailWord_2025015).sum := by decide
  have hdescent : baseEnd_2025015 < baseStart_2025015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025047 : List Nat := [1, 1, 3, 2, 2, 3, 4, 2, 4]
def baseStart_2025047 : Nat := 118140960795 + 2025047 * 2 ^ 59
def prefixEnd_2025047 : Nat := 4983230072969 + 3 ^ 40 * 2025047 * 2
def baseEnd_2025047 : Nat := 231071657543431939555441

theorem tailTrace_2025047 : CollatzResearch.WordTrace tailWord_2025047 prefixEnd_2025047 231071657543431939555441 := by
  unfold tailWord_2025047
  simp only [CollatzResearch.WordTrace]
  refine ⟨73859531894608044338145395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49239687929738696225430263 73859531894608044338145395)
  ·
    refine ⟨110789297841912066507218093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73859531894608044338145395 110789297841912066507218093)
    ·
      refine ⟨41545986690717024940206785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110789297841912066507218093 41545986690717024940206785)
      ·
        refine ⟨31159490018037768705155089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41545986690717024940206785 31159490018037768705155089)
        ·
          refine ⟨23369617513528326528866317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31159490018037768705155089 23369617513528326528866317)
          ·
            refine ⟨8763606567573122448324869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23369617513528326528866317 8763606567573122448324869)
            ·
              refine ⟨1643176231419960459060913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8763606567573122448324869 1643176231419960459060913)
              ·
                refine ⟨1232382173564970344295685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643176231419960459060913 1232382173564970344295685)
                ·
                  refine ⟨231071657543431939555441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1232382173564970344295685 231071657543431939555441)
                  ·
                    rfl

theorem cell22_2025047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 4].length) (baseStart_2025047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025047 prefixEnd_2025047 := by exact prefixLift 2025047
  have htrace : WordTrace (prefixWord ++ tailWord_2025047) baseStart_2025047 baseEnd_2025047 := by
    simpa [prefixWord, tailWord_2025047, baseEnd_2025047] using wordTrace_append hprefix tailTrace_2025047
  have hstable : (prefixWord ++ tailWord_2025047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025047).length < 2 ^ (prefixWord ++ tailWord_2025047).sum := by decide
  have hdescent : baseEnd_2025047 < baseStart_2025047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025077 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 2, 4]
def baseStart_2025077 : Nat := 118140960795 + 2025077 * 2 ^ 59
def prefixEnd_2025077 : Nat := 4983230072969 + 3 ^ 40 * 2025077 * 2
def baseEnd_2025077 : Nat := 693225242243385740416231

theorem tailTrace_2025077 : CollatzResearch.WordTrace tailWord_2025077 prefixEnd_2025077 693225242243385740416231 := by
  unfold tailWord_2025077
  simp only [CollatzResearch.WordTrace]
  refine ⟨73860626084499359461737485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49240417389666239641158323 73860626084499359461737485)
  ·
    refine ⟨27697734781687259798151557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73860626084499359461737485 27697734781687259798151557)
    ·
      refine ⟨5193325271566361212153417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27697734781687259798151557 5193325271566361212153417)
      ·
        refine ⟨3894993953674770909115063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5193325271566361212153417 3894993953674770909115063)
        ·
          refine ⟨5842490930512156363672595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894993953674770909115063 5842490930512156363672595)
          ·
            refine ⟨8763736395768234545508893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5842490930512156363672595 8763736395768234545508893)
            ·
              refine ⟨3286401148413087954565835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8763736395768234545508893 3286401148413087954565835)
              ·
                refine ⟨4929601722619631931848753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286401148413087954565835 4929601722619631931848753)
                ·
                  refine ⟨3697201291964723948886565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4929601722619631931848753 3697201291964723948886565)
                  ·
                    refine ⟨693225242243385740416231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3697201291964723948886565 693225242243385740416231)
                    ·
                      rfl

theorem cell22_2025077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_2025077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025077 prefixEnd_2025077 := by exact prefixLift 2025077
  have htrace : WordTrace (prefixWord ++ tailWord_2025077) baseStart_2025077 baseEnd_2025077 := by
    simpa [prefixWord, tailWord_2025077, baseEnd_2025077] using wordTrace_append hprefix tailTrace_2025077
  have hstable : (prefixWord ++ tailWord_2025077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025077).length < 2 ^ (prefixWord ++ tailWord_2025077).sum := by decide
  have hdescent : baseEnd_2025077 < baseStart_2025077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025096 : List Nat := [2, 1, 3, 5, 1, 2, 1, 2, 2, 3]
def baseStart_2025096 : Nat := 118140960795 + 2025096 * 2 ^ 59
def prefixEnd_2025096 : Nat := 4983230072969 + 3 ^ 40 * 2025096 * 2
def baseEnd_2025096 : Nat := 693231746331676024191173

theorem tailTrace_2025096 : CollatzResearch.WordTrace tailWord_2025096 prefixEnd_2025096 693231746331676024191173 := by
  unfold tailWord_2025096
  simp only [CollatzResearch.WordTrace]
  refine ⟨36930659535715262853339571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49240879380953683804452761 36930659535715262853339571)
  ·
    refine ⟨55395989303572894280009357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36930659535715262853339571 55395989303572894280009357)
    ·
      refine ⟨20773495988839835355003509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55395989303572894280009357 20773495988839835355003509)
      ·
        refine ⟨1947515248953734564531579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20773495988839835355003509 1947515248953734564531579)
        ·
          refine ⟨2921272873430601846797369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947515248953734564531579 2921272873430601846797369)
          ·
            refine ⟨2190954655072951385098027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2921272873430601846797369 2190954655072951385098027)
            ·
              refine ⟨3286431982609427077647041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190954655072951385098027 3286431982609427077647041)
              ·
                refine ⟨2464823986957070308235281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3286431982609427077647041 2464823986957070308235281)
                ·
                  refine ⟨1848617990217802731176461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2464823986957070308235281 1848617990217802731176461)
                  ·
                    refine ⟨693231746331676024191173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1848617990217802731176461 693231746331676024191173)
                    ·
                      rfl

theorem cell22_2025096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_2025096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025096 prefixEnd_2025096 := by exact prefixLift 2025096
  have htrace : WordTrace (prefixWord ++ tailWord_2025096) baseStart_2025096 baseEnd_2025096 := by
    simpa [prefixWord, tailWord_2025096, baseEnd_2025096] using wordTrace_append hprefix tailTrace_2025096
  have hstable : (prefixWord ++ tailWord_2025096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025096).length < 2 ^ (prefixWord ++ tailWord_2025096).sum := by decide
  have hdescent : baseEnd_2025096 < baseStart_2025096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025158 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2025158 : Nat := 118140960795 + 2025158 * 2 ^ 59
def prefixEnd_2025158 : Nat := 4983230072969 + 3 ^ 40 * 2025158 * 2
def baseEnd_2025158 : Nat := 693252970198728529140983

theorem tailTrace_2025158 : CollatzResearch.WordTrace tailWord_2025158 prefixEnd_2025158 693252970198728529140983 := by
  unfold tailWord_2025158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2308236887412684696732379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49242386931470606863624085 2308236887412684696732379)
  ·
    refine ⟨3462355331119027045098569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2308236887412684696732379 3462355331119027045098569)
    ·
      refine ⟨2596766498339270283823927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3462355331119027045098569 2596766498339270283823927)
      ·
        refine ⟨3895149747508905425735891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2596766498339270283823927 3895149747508905425735891)
        ·
          refine ⟨5842724621263358138603837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3895149747508905425735891 5842724621263358138603837)
          ·
            refine ⟨2191021732973759301976439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5842724621263358138603837 2191021732973759301976439)
            ·
              refine ⟨3286532599460638952964659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2191021732973759301976439 3286532599460638952964659)
              ·
                refine ⟨4929798899190958429446989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286532599460638952964659 4929798899190958429446989)
                ·
                  refine ⟨1848674587196609411042621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4929798899190958429446989 1848674587196609411042621)
                  ·
                    refine ⟨693252970198728529140983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1848674587196609411042621 693252970198728529140983)
                    ·
                      rfl

theorem cell22_2025158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2025158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025158 prefixEnd_2025158 := by exact prefixLift 2025158
  have htrace : WordTrace (prefixWord ++ tailWord_2025158) baseStart_2025158 baseEnd_2025158 := by
    simpa [prefixWord, tailWord_2025158, baseEnd_2025158] using wordTrace_append hprefix tailTrace_2025158
  have hstable : (prefixWord ++ tailWord_2025158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025158).length < 2 ^ (prefixWord ++ tailWord_2025158).sum := by decide
  have hdescent : baseEnd_2025158 < baseStart_2025158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025195 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 2, 4]
def baseStart_2025195 : Nat := 118140960795 + 2025195 * 2 ^ 59
def prefixEnd_2025195 : Nat := 4983230072969 + 3 ^ 40 * 2025195 * 2
def baseEnd_2025195 : Nat := 693265636054872765965869

theorem tailTrace_2025195 : CollatzResearch.WordTrace tailWord_2025195 prefixEnd_2025195 693265636054872765965869 := by
  unfold tailWord_2025195
  simp only [CollatzResearch.WordTrace]
  refine ⟨73864929898071865614533039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49243286598714577076355359 73864929898071865614533039)
  ·
    refine ⟨110797394847107798421799559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73864929898071865614533039 110797394847107798421799559)
    ·
      refine ⟨166196092270661697632699339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110797394847107798421799559 166196092270661697632699339)
      ·
        refine ⟨249294138405992546449049009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166196092270661697632699339 249294138405992546449049009)
        ·
          refine ⟨186970603804494409836786757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249294138405992546449049009 186970603804494409836786757)
          ·
            refine ⟨35056988213342701844397517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186970603804494409836786757 35056988213342701844397517)
            ·
              refine ⟨13146370580003513191649069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35056988213342701844397517 13146370580003513191649069)
              ·
                refine ⟨4929888967501317446868401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13146370580003513191649069 4929888967501317446868401)
                ·
                  refine ⟨3697416725625988085151301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4929888967501317446868401 3697416725625988085151301)
                  ·
                    refine ⟨693265636054872765965869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3697416725625988085151301 693265636054872765965869)
                    ·
                      rfl

theorem cell22_2025195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 4].length) (baseStart_2025195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025195 prefixEnd_2025195 := by exact prefixLift 2025195
  have htrace : WordTrace (prefixWord ++ tailWord_2025195) baseStart_2025195 baseEnd_2025195 := by
    simpa [prefixWord, tailWord_2025195, baseEnd_2025195] using wordTrace_append hprefix tailTrace_2025195
  have hstable : (prefixWord ++ tailWord_2025195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025195).length < 2 ^ (prefixWord ++ tailWord_2025195).sum := by decide
  have hdescent : baseEnd_2025195 < baseStart_2025195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025197 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_2025197 : Nat := 118140960795 + 2025197 * 2 ^ 59
def prefixEnd_2025197 : Nat := 4983230072969 + 3 ^ 40 * 2025197 * 2
def baseEnd_2025197 : Nat := 693266320695745427415863

theorem tailTrace_2025197 : CollatzResearch.WordTrace tailWord_2025197 prefixEnd_2025197 693266320695745427415863 := by
  unfold tailWord_2025197
  simp only [CollatzResearch.WordTrace]
  refine ⟨73865002844064619956105845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49243335229376413304070563 73865002844064619956105845)
  ·
    refine ⟨6924844016631058120884923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73865002844064619956105845 6924844016631058120884923)
    ·
      refine ⟨10387266024946587181327385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6924844016631058120884923 10387266024946587181327385)
      ·
        refine ⟨7790449518709940385995539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10387266024946587181327385 7790449518709940385995539)
        ·
          refine ⟨11685674278064910578993309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7790449518709940385995539 11685674278064910578993309)
          ·
            refine ⟨4382127854274341467122491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11685674278064910578993309 4382127854274341467122491)
            ·
              refine ⟨6573191781411512200683737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382127854274341467122491 6573191781411512200683737)
              ·
                refine ⟨4929893836058634150512803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6573191781411512200683737 4929893836058634150512803)
                ·
                  refine ⟨7394840754087951225769205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929893836058634150512803 7394840754087951225769205)
                  ·
                    refine ⟨693266320695745427415863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7394840754087951225769205 693266320695745427415863)
                    ·
                      rfl

theorem cell22_2025197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_2025197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025197 prefixEnd_2025197 := by exact prefixLift 2025197
  have htrace : WordTrace (prefixWord ++ tailWord_2025197) baseStart_2025197 baseEnd_2025197 := by
    simpa [prefixWord, tailWord_2025197, baseEnd_2025197] using wordTrace_append hprefix tailTrace_2025197
  have hstable : (prefixWord ++ tailWord_2025197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025197).length < 2 ^ (prefixWord ++ tailWord_2025197).sum := by decide
  have hdescent : baseEnd_2025197 < baseStart_2025197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025242 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 5, 3]
def baseStart_2025242 : Nat := 118140960795 + 2025242 * 2 ^ 59
def prefixEnd_2025242 : Nat := 4983230072969 + 3 ^ 40 * 2025242 * 2
def baseEnd_2025242 : Nat := 693281725115380310040725

theorem tailTrace_2025242 : CollatzResearch.WordTrace tailWord_2025242 prefixEnd_2025242 693281725115380310040725 := by
  unfold tailWord_2025242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18466661032225398160373495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49244429419267728427662653 18466661032225398160373495)
  ·
    refine ⟨27699991548338097240560243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18466661032225398160373495 27699991548338097240560243)
    ·
      refine ⟨41549987322507145860840365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27699991548338097240560243 41549987322507145860840365)
      ·
        refine ⟨15581245245940179697815137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41549987322507145860840365 15581245245940179697815137)
        ·
          refine ⟨11685933934455134773361353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15581245245940179697815137 11685933934455134773361353)
          ·
            refine ⟨8764450450841351080021015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11685933934455134773361353 8764450450841351080021015)
            ·
              refine ⟨13146675676262026620031523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764450450841351080021015 13146675676262026620031523)
              ·
                refine ⟨19720013514393039930047285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13146675676262026620031523 19720013514393039930047285)
                ·
                  refine ⟨1848751266974347493441933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19720013514393039930047285 1848751266974347493441933)
                  ·
                    refine ⟨693281725115380310040725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1848751266974347493441933 693281725115380310040725)
                    ·
                      rfl

theorem cell22_2025242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_2025242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025242 prefixEnd_2025242 := by exact prefixLift 2025242
  have htrace : WordTrace (prefixWord ++ tailWord_2025242) baseStart_2025242 baseEnd_2025242 := by
    simpa [prefixWord, tailWord_2025242, baseEnd_2025242] using wordTrace_append hprefix tailTrace_2025242
  have hstable : (prefixWord ++ tailWord_2025242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025242).length < 2 ^ (prefixWord ++ tailWord_2025242).sum := by decide
  have hdescent : baseEnd_2025242 < baseStart_2025242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025246 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_2025246 : Nat := 118140960795 + 2025246 * 2 ^ 59
def prefixEnd_2025246 : Nat := 4983230072969 + 3 ^ 40 * 2025246 * 2
def baseEnd_2025246 : Nat := 693283094397125632940713

theorem tailTrace_2025246 : CollatzResearch.WordTrace tailWord_2025246 prefixEnd_2025246 693283094397125632940713 := by
  unfold tailWord_2025246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9233348752610887665579949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49244526680591400883093061 9233348752610887665579949)
  ·
    refine ⟨3462505782229082874592481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9233348752610887665579949 3462505782229082874592481)
    ·
      refine ⟨2596879336671812155944361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3462505782229082874592481 2596879336671812155944361)
      ·
        refine ⟨1947659502503859116958271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2596879336671812155944361 1947659502503859116958271)
        ·
          refine ⟨2921489253755788675437407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947659502503859116958271 2921489253755788675437407)
          ·
            refine ⟨4382233880633683013156111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921489253755788675437407 4382233880633683013156111)
            ·
              refine ⟨6573350820950524519734167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382233880633683013156111 6573350820950524519734167)
              ·
                refine ⟨9860026231425786779601251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6573350820950524519734167 9860026231425786779601251)
                ·
                  refine ⟨14790039347138680169401877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9860026231425786779601251 14790039347138680169401877)
                  ·
                    refine ⟨693283094397125632940713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14790039347138680169401877 693283094397125632940713)
                    ·
                      rfl

theorem cell22_2025246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_2025246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025246 prefixEnd_2025246 := by exact prefixLift 2025246
  have htrace : WordTrace (prefixWord ++ tailWord_2025246) baseStart_2025246 baseEnd_2025246 := by
    simpa [prefixWord, tailWord_2025246, baseEnd_2025246] using wordTrace_append hprefix tailTrace_2025246
  have hstable : (prefixWord ++ tailWord_2025246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025246).length < 2 ^ (prefixWord ++ tailWord_2025246).sum := by decide
  have hdescent : baseEnd_2025246 < baseStart_2025246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025272 : List Nat := [2, 1, 2, 1, 3, 3, 3, 2, 5]
def baseStart_2025272 : Nat := 118140960795 + 2025272 * 2 ^ 59
def prefixEnd_2025272 : Nat := 4983230072969 + 3 ^ 40 * 2025272 * 2
def baseEnd_2025272 : Nat := 231097331576156743930211

theorem tailTrace_2025272 : CollatzResearch.WordTrace tailWord_2025272 prefixEnd_2025272 231097331576156743930211 := by
  unfold tailWord_2025272
  simp only [CollatzResearch.WordTrace]
  refine ⟨36933869159396453882543035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49245158879195271843390713 36933869159396453882543035)
  ·
    refine ⟨55400803739094680823814553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36933869159396453882543035 55400803739094680823814553)
    ·
      refine ⟨41550602804321010617860915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55400803739094680823814553 41550602804321010617860915)
      ·
        refine ⟨62325904206481515926791373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41550602804321010617860915 62325904206481515926791373)
        ·
          refine ⟨23372214077430568472546765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62325904206481515926791373 23372214077430568472546765)
          ·
            refine ⟨8764580279036463177205037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23372214077430568472546765 8764580279036463177205037)
            ·
              refine ⟨3286717604638673691451889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8764580279036463177205037 3286717604638673691451889)
              ·
                refine ⟨2465038203479005268588917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3286717604638673691451889 2465038203479005268588917)
                ·
                  refine ⟨231097331576156743930211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2465038203479005268588917 231097331576156743930211)
                  ·
                    rfl

theorem cell22_2025272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 5].length) (baseStart_2025272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025272 prefixEnd_2025272 := by exact prefixLift 2025272
  have htrace : WordTrace (prefixWord ++ tailWord_2025272) baseStart_2025272 baseEnd_2025272 := by
    simpa [prefixWord, tailWord_2025272, baseEnd_2025272] using wordTrace_append hprefix tailTrace_2025272
  have hstable : (prefixWord ++ tailWord_2025272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025272).length < 2 ^ (prefixWord ++ tailWord_2025272).sum := by decide
  have hdescent : baseEnd_2025272 < baseStart_2025272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025349 : List Nat := [1, 3, 1, 1, 3, 2, 3, 3, 2, 3]
def baseStart_2025349 : Nat := 118140960795 + 2025349 * 2 ^ 59
def prefixEnd_2025349 : Nat := 4983230072969 + 3 ^ 40 * 2025349 * 2
def baseEnd_2025349 : Nat := 693318353402067697615397

theorem tailTrace_2025349 : CollatzResearch.WordTrace tailWord_2025349 prefixEnd_2025349 693318353402067697615397 := by
  unfold tailWord_2025349
  simp only [CollatzResearch.WordTrace]
  refine ⟨73870546739513949915639101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49247031159675966610426067 73870546739513949915639101)
  ·
    refine ⟨27701455027317731218364663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73870546739513949915639101 27701455027317731218364663)
    ·
      refine ⟨41552182540976596827546995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27701455027317731218364663 41552182540976596827546995)
      ·
        refine ⟨62328273811464895241320493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41552182540976596827546995 62328273811464895241320493)
        ·
          refine ⟨23373102679299335715495185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62328273811464895241320493 23373102679299335715495185)
          ·
            refine ⟨17529827009474501786621389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23373102679299335715495185 17529827009474501786621389)
            ·
              refine ⟨6573685128552938169983021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17529827009474501786621389 6573685128552938169983021)
              ·
                refine ⟨2465131923207351813743633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6573685128552938169983021 2465131923207351813743633)
                ·
                  refine ⟨1848848942405513860307725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2465131923207351813743633 1848848942405513860307725)
                  ·
                    refine ⟨693318353402067697615397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1848848942405513860307725 693318353402067697615397)
                    ·
                      rfl

theorem cell22_2025349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_2025349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025349 prefixEnd_2025349 := by exact prefixLift 2025349
  have htrace : WordTrace (prefixWord ++ tailWord_2025349) baseStart_2025349 baseEnd_2025349 := by
    simpa [prefixWord, tailWord_2025349, baseEnd_2025349] using wordTrace_append hprefix tailTrace_2025349
  have hstable : (prefixWord ++ tailWord_2025349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025349).length < 2 ^ (prefixWord ++ tailWord_2025349).sum := by decide
  have hdescent : baseEnd_2025349 < baseStart_2025349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025360 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 1, 9]
def baseStart_2025360 : Nat := 118140960795 + 2025360 * 2 ^ 59
def prefixEnd_2025360 : Nat := 4983230072969 + 3 ^ 40 * 2025360 * 2
def baseEnd_2025360 : Nat := 693322118926867335590363

theorem tailTrace_2025360 : CollatzResearch.WordTrace tailWord_2025360 prefixEnd_2025360 693322118926867335590363 := by
  unfold tailWord_2025360
  simp only [CollatzResearch.WordTrace]
  refine ⟨36935473971237049397144767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49247298628316065862859689 36935473971237049397144767)
  ·
    refine ⟨55403210956855574095717151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36935473971237049397144767 55403210956855574095717151)
    ·
      refine ⟨83104816435283361143575727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55403210956855574095717151 83104816435283361143575727)
      ·
        refine ⟨124657224652925041715363591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83104816435283361143575727 124657224652925041715363591)
        ·
          refine ⟨186985836979387562573045387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124657224652925041715363591 186985836979387562573045387)
          ·
            refine ⟨280478755469081343859568081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186985836979387562573045387 280478755469081343859568081)
            ·
              refine ⟨210359066601811007894676061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280478755469081343859568081 210359066601811007894676061)
              ·
                refine ⟨78884649975679127960503523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210359066601811007894676061 78884649975679127960503523)
                ·
                  refine ⟨118326974963518691940755285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78884649975679127960503523 118326974963518691940755285)
                  ·
                    refine ⟨693322118926867335590363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 118326974963518691940755285 693322118926867335590363)
                    ·
                      rfl

theorem cell22_2025360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_2025360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025360 prefixEnd_2025360 := by exact prefixLift 2025360
  have htrace : WordTrace (prefixWord ++ tailWord_2025360) baseStart_2025360 baseEnd_2025360 := by
    simpa [prefixWord, tailWord_2025360, baseEnd_2025360] using wordTrace_append hprefix tailTrace_2025360
  have hstable : (prefixWord ++ tailWord_2025360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025360).length < 2 ^ (prefixWord ++ tailWord_2025360).sum := by decide
  have hdescent : baseEnd_2025360 < baseStart_2025360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025364 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2025364 : Nat := 118140960795 + 2025364 * 2 ^ 59
def prefixEnd_2025364 : Nat := 4983230072969 + 3 ^ 40 * 2025364 * 2
def baseEnd_2025364 : Nat := 693323488208612658490351

theorem tailTrace_2025364 : CollatzResearch.WordTrace tailWord_2025364 prefixEnd_2025364 693323488208612658490351 := by
  unfold tailWord_2025364
  simp only [CollatzResearch.WordTrace]
  refine ⟨36935546917229803738717573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49247395889639738318290097 36935546917229803738717573)
  ·
    refine ⟨6925415046980588201009545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36935546917229803738717573 6925415046980588201009545)
    ·
      refine ⟨5194061285235441150757159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6925415046980588201009545 5194061285235441150757159)
      ·
        refine ⟨7791091927853161726135739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5194061285235441150757159 7791091927853161726135739)
        ·
          refine ⟨11686637891779742589203609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7791091927853161726135739 11686637891779742589203609)
          ·
            refine ⟨8764978418834806941902707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11686637891779742589203609 8764978418834806941902707)
            ·
              refine ⟨13147467628252210412854061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764978418834806941902707 13147467628252210412854061)
              ·
                refine ⟨4930300360594578904820273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13147467628252210412854061 4930300360594578904820273)
                ·
                  refine ⟨3697725270445934178615205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4930300360594578904820273 3697725270445934178615205)
                  ·
                    refine ⟨693323488208612658490351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3697725270445934178615205 693323488208612658490351)
                    ·
                      rfl

theorem cell22_2025364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2025364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025364 prefixEnd_2025364 := by exact prefixLift 2025364
  have htrace : WordTrace (prefixWord ++ tailWord_2025364) baseStart_2025364 baseEnd_2025364 := by
    simpa [prefixWord, tailWord_2025364, baseEnd_2025364] using wordTrace_append hprefix tailTrace_2025364
  have hstable : (prefixWord ++ tailWord_2025364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025364).length < 2 ^ (prefixWord ++ tailWord_2025364).sum := by decide
  have hdescent : baseEnd_2025364 < baseStart_2025364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025407 : List Nat := [1, 1, 2, 2, 2, 1, 3, 5, 5]
def baseStart_2025407 : Nat := 118140960795 + 2025407 * 2 ^ 59
def prefixEnd_2025407 : Nat := 4983230072969 + 3 ^ 40 * 2025407 * 2
def baseEnd_2025407 : Nat := 231112735995791626555073

theorem tailTrace_2025407 : CollatzResearch.WordTrace tailWord_2025407 prefixEnd_2025407 231112735995791626555073 := by
  unfold tailWord_2025407
  simp only [CollatzResearch.WordTrace]
  refine ⟨73872662173303825821250475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49248441448869217214166983 73872662173303825821250475)
  ·
    refine ⟨110808993259955738731875713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73872662173303825821250475 110808993259955738731875713)
    ·
      refine ⟨83106744944966804048906785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110808993259955738731875713 83106744944966804048906785)
      ·
        refine ⟨62330058708725103036680089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83106744944966804048906785 62330058708725103036680089)
        ·
          refine ⟨46747544031543827277510067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62330058708725103036680089 46747544031543827277510067)
          ·
            refine ⟨70121316047315740916265101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46747544031543827277510067 70121316047315740916265101)
            ·
              refine ⟨26295493517743402843599413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70121316047315740916265101 26295493517743402843599413)
              ·
                refine ⟨2465202517288444016587445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26295493517743402843599413 2465202517288444016587445)
                ·
                  refine ⟨231112735995791626555073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2465202517288444016587445 231112735995791626555073)
                  ·
                    rfl

theorem cell22_2025407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 5].length) (baseStart_2025407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025407 prefixEnd_2025407 := by exact prefixLift 2025407
  have htrace : WordTrace (prefixWord ++ tailWord_2025407) baseStart_2025407 baseEnd_2025407 := by
    simpa [prefixWord, tailWord_2025407, baseEnd_2025407] using wordTrace_append hprefix tailTrace_2025407
  have hstable : (prefixWord ++ tailWord_2025407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025407).length < 2 ^ (prefixWord ++ tailWord_2025407).sum := by decide
  have hdescent : baseEnd_2025407 < baseStart_2025407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025422 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_2025422 : Nat := 118140960795 + 2025422 * 2 ^ 59
def prefixEnd_2025422 : Nat := 4983230072969 + 3 ^ 40 * 2025422 * 2
def baseEnd_2025422 : Nat := 693343342793919840540173

theorem tailTrace_2025422 : CollatzResearch.WordTrace tailWord_2025422 prefixEnd_2025422 693343342793919840540173 := by
  unfold tailWord_2025422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9234151158531185422880815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49248806178832988922031013 9234151158531185422880815)
  ·
    refine ⟨13851226737796778134321223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9234151158531185422880815 13851226737796778134321223)
    ·
      refine ⟨20776840106695167201481835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13851226737796778134321223 20776840106695167201481835)
      ·
        refine ⟨31165260160042750802222753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20776840106695167201481835 31165260160042750802222753)
        ·
          refine ⟨23373945120032063101667065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31165260160042750802222753 23373945120032063101667065)
          ·
            refine ⟨17530458840024047326250299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23373945120032063101667065 17530458840024047326250299)
            ·
              refine ⟨26295688260036070989375449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17530458840024047326250299 26295688260036070989375449)
              ·
                refine ⟨19721766195027053242031587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26295688260036070989375449 19721766195027053242031587)
                ·
                  refine ⟨29582649292540579863047381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19721766195027053242031587 29582649292540579863047381)
                  ·
                    refine ⟨693343342793919840540173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29582649292540579863047381 693343342793919840540173)
                    ·
                      rfl

theorem cell22_2025422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_2025422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025422 prefixEnd_2025422 := by exact prefixLift 2025422
  have htrace : WordTrace (prefixWord ++ tailWord_2025422) baseStart_2025422 baseEnd_2025422 := by
    simpa [prefixWord, tailWord_2025422, baseEnd_2025422] using wordTrace_append hprefix tailTrace_2025422
  have hstable : (prefixWord ++ tailWord_2025422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025422).length < 2 ^ (prefixWord ++ tailWord_2025422).sum := by decide
  have hdescent : baseEnd_2025422 < baseStart_2025422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025428 : List Nat := [2, 4, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_2025428 : Nat := 118140960795 + 2025428 * 2 ^ 59
def prefixEnd_2025428 : Nat := 4983230072969 + 3 ^ 40 * 2025428 * 2
def baseEnd_2025428 : Nat := 693345396716537824890155

theorem tailTrace_2025428 : CollatzResearch.WordTrace tailWord_2025428 prefixEnd_2025428 693345396716537824890155 := by
  unfold tailWord_2025428
  simp only [CollatzResearch.WordTrace]
  refine ⟨36936714053113873203882469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49248952070818497605176625 36936714053113873203882469)
  ·
    refine ⟨6925633884958851225727963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36936714053113873203882469 6925633884958851225727963)
    ·
      refine ⟨10388450827438276838591945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6925633884958851225727963 10388450827438276838591945)
      ·
        refine ⟨7791338120578707628943959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10388450827438276838591945 7791338120578707628943959)
        ·
          refine ⟨11687007180868061443415939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7791338120578707628943959 11687007180868061443415939)
          ·
            refine ⟨17530510771302092165123909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11687007180868061443415939 17530510771302092165123909)
            ·
              refine ⟨3286970769619142280960733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17530510771302092165123909 3286970769619142280960733)
              ·
                refine ⟨1232614038607178355360275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3286970769619142280960733 1232614038607178355360275)
                ·
                  refine ⟨1848921057910767533040413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232614038607178355360275 1848921057910767533040413)
                  ·
                    refine ⟨693345396716537824890155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1848921057910767533040413 693345396716537824890155)
                    ·
                      rfl

theorem cell22_2025428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_2025428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025428 prefixEnd_2025428 := by exact prefixLift 2025428
  have htrace : WordTrace (prefixWord ++ tailWord_2025428) baseStart_2025428 baseEnd_2025428 := by
    simpa [prefixWord, tailWord_2025428, baseEnd_2025428] using wordTrace_append hprefix tailTrace_2025428
  have hstable : (prefixWord ++ tailWord_2025428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025428).length < 2 ^ (prefixWord ++ tailWord_2025428).sum := by decide
  have hdescent : baseEnd_2025428 < baseStart_2025428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025484 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 6, 3]
def baseStart_2025484 : Nat := 118140960795 + 2025484 * 2 ^ 59
def prefixEnd_2025484 : Nat := 4983230072969 + 3 ^ 40 * 2025484 * 2
def baseEnd_2025484 : Nat := 693364566660972345489983

theorem tailTrace_2025484 : CollatzResearch.WordTrace tailWord_2025484 prefixEnd_2025484 693364566660972345489983 := by
  unfold tailWord_2025484
  simp only [CollatzResearch.WordTrace]
  refine ⟨36937735297012433985901753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49250313729349911981202337 36937735297012433985901753)
  ·
    refine ⟨27703301472759325489426315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36937735297012433985901753 27703301472759325489426315)
    ·
      refine ⟨41554952209138988234139473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27703301472759325489426315 41554952209138988234139473)
      ·
        refine ⟨31166214156854241175604605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41554952209138988234139473 31166214156854241175604605)
        ·
          refine ⟨11687330308820340440851727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31166214156854241175604605 11687330308820340440851727)
          ·
            refine ⟨17530995463230510661277591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11687330308820340440851727 17530995463230510661277591)
            ·
              refine ⟨26296493194845765991916387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17530995463230510661277591 26296493194845765991916387)
              ·
                refine ⟨39444739792268648987874581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26296493194845765991916387 39444739792268648987874581)
                ·
                  refine ⟨1848972177762592921306621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39444739792268648987874581 1848972177762592921306621)
                  ·
                    refine ⟨693364566660972345489983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1848972177762592921306621 693364566660972345489983)
                    ·
                      rfl

theorem cell22_2025484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_2025484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025484 prefixEnd_2025484 := by exact prefixLift 2025484
  have htrace : WordTrace (prefixWord ++ tailWord_2025484) baseStart_2025484 baseEnd_2025484 := by
    simpa [prefixWord, tailWord_2025484, baseEnd_2025484] using wordTrace_append hprefix tailTrace_2025484
  have hstable : (prefixWord ++ tailWord_2025484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025484).length < 2 ^ (prefixWord ++ tailWord_2025484).sum := by decide
  have hdescent : baseEnd_2025484 < baseStart_2025484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025501 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_2025501 : Nat := 118140960795 + 2025501 * 2 ^ 59
def prefixEnd_2025501 : Nat := 4983230072969 + 3 ^ 40 * 2025501 * 2
def baseEnd_2025501 : Nat := 693370386108389967814931

theorem tailTrace_2025501 : CollatzResearch.WordTrace tailWord_2025501 prefixEnd_2025501 693370386108389967814931 := by
  unfold tailWord_2025501
  simp only [CollatzResearch.WordTrace]
  refine ⟨73876090634963279875172357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49250727089975519916781571 73876090634963279875172357)
  ·
    refine ⟨13851766994055614976594817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73876090634963279875172357 13851766994055614976594817)
    ·
      refine ⟨10388825245541711232446113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13851766994055614976594817 10388825245541711232446113)
      ·
        refine ⟨7791618934156283424334585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10388825245541711232446113 7791618934156283424334585)
        ·
          refine ⟨5843714200617212568250939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7791618934156283424334585 5843714200617212568250939)
          ·
            refine ⟨8765571300925818852376409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5843714200617212568250939 8765571300925818852376409)
            ·
              refine ⟨6574178475694364139282307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8765571300925818852376409 6574178475694364139282307)
              ·
                refine ⟨9861267713541546208923461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6574178475694364139282307 9861267713541546208923461)
                ·
                  refine ⟨1848987696289039914173149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9861267713541546208923461 1848987696289039914173149)
                  ·
                    refine ⟨693370386108389967814931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1848987696289039914173149 693370386108389967814931)
                    ·
                      rfl

theorem cell22_2025501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_2025501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025501 prefixEnd_2025501 := by exact prefixLift 2025501
  have htrace : WordTrace (prefixWord ++ tailWord_2025501) baseStart_2025501 baseEnd_2025501 := by
    simpa [prefixWord, tailWord_2025501, baseEnd_2025501] using wordTrace_append hprefix tailTrace_2025501
  have hstable : (prefixWord ++ tailWord_2025501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025501).length < 2 ^ (prefixWord ++ tailWord_2025501).sum := by decide
  have hdescent : baseEnd_2025501 < baseStart_2025501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025514 : List Nat := [3, 1, 4, 1, 2, 1, 1, 9]
def baseStart_2025514 : Nat := 118140960795 + 2025514 * 2 ^ 59
def prefixEnd_2025514 : Nat := 4983230072969 + 3 ^ 40 * 2025514 * 2
def baseEnd_2025514 : Nat := 77041648474895807471099

theorem tailTrace_2025514 : CollatzResearch.WordTrace tailWord_2025514 prefixEnd_2025514 77041648474895807471099 := by
  unfold tailWord_2025514
  simp only [CollatzResearch.WordTrace]
  refine ⟨18469141195979045773848899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49251043189277455396930397 18469141195979045773848899)
  ·
    refine ⟨27703711793968568660773349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18469141195979045773848899 27703711793968568660773349)
    ·
      refine ⟨5194445961369106623895003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27703711793968568660773349 5194445961369106623895003)
      ·
        refine ⟨7791668942053659935842505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5194445961369106623895003 7791668942053659935842505)
        ·
          refine ⟨5843751706540244951881879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7791668942053659935842505 5843751706540244951881879)
          ·
            refine ⟨8765627559810367427822819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5843751706540244951881879 8765627559810367427822819)
            ·
              refine ⟨13148441339715551141734229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8765627559810367427822819 13148441339715551141734229)
              ·
                refine ⟨77041648474895807471099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13148441339715551141734229 77041648474895807471099)
                ·
                  rfl

theorem cell22_2025514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_2025514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025514 prefixEnd_2025514 := by exact prefixLift 2025514
  have htrace : WordTrace (prefixWord ++ tailWord_2025514) baseStart_2025514 baseEnd_2025514 := by
    simpa [prefixWord, tailWord_2025514, baseEnd_2025514] using wordTrace_append hprefix tailTrace_2025514
  have hstable : (prefixWord ++ tailWord_2025514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025514).length < 2 ^ (prefixWord ++ tailWord_2025514).sum := by decide
  have hdescent : baseEnd_2025514 < baseStart_2025514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025518 : List Nat := [4, 1, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2025518 : Nat := 118140960795 + 2025518 * 2 ^ 59
def prefixEnd_2025518 : Nat := 4983230072969 + 3 ^ 40 * 2025518 * 2
def baseEnd_2025518 : Nat := 693376205555807590139879

theorem tailTrace_2025518 : CollatzResearch.WordTrace tailWord_2025518 prefixEnd_2025518 693376205555807590139879 := by
  unfold tailWord_2025518
  simp only [CollatzResearch.WordTrace]
  refine ⟨9234588834487711472317651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49251140450601127852360805 9234588834487711472317651)
  ·
    refine ⟨13851883251731567208476477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9234588834487711472317651 13851883251731567208476477)
    ·
      refine ⟨5194456219399337703178679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13851883251731567208476477 5194456219399337703178679)
      ·
        refine ⟨7791684329099006554768019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5194456219399337703178679 7791684329099006554768019)
        ·
          refine ⟨11687526493648509832152029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7791684329099006554768019 11687526493648509832152029)
          ·
            refine ⟨4382822435118191187057011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11687526493648509832152029 4382822435118191187057011)
            ·
              refine ⟨6574233652677286780585517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382822435118191187057011 6574233652677286780585517)
              ·
                refine ⟨2465337619753982542719569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6574233652677286780585517 2465337619753982542719569)
                ·
                  refine ⟨1849003214815486907039677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2465337619753982542719569 1849003214815486907039677)
                  ·
                    refine ⟨693376205555807590139879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1849003214815486907039677 693376205555807590139879)
                    ·
                      rfl

theorem cell22_2025518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2025518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025518 prefixEnd_2025518 := by exact prefixLift 2025518
  have htrace : WordTrace (prefixWord ++ tailWord_2025518) baseStart_2025518 baseEnd_2025518 := by
    simpa [prefixWord, tailWord_2025518, baseEnd_2025518] using wordTrace_append hprefix tailTrace_2025518
  have hstable : (prefixWord ++ tailWord_2025518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025518).length < 2 ^ (prefixWord ++ tailWord_2025518).sum := by decide
  have hdescent : baseEnd_2025518 < baseStart_2025518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025559 : List Nat := [1, 1, 3, 2, 2, 1, 3, 4, 5]
def baseStart_2025559 : Nat := 118140960795 + 2025559 * 2 ^ 59
def prefixEnd_2025559 : Nat := 4983230072969 + 3 ^ 40 * 2025559 * 2
def baseEnd_2025559 : Nat := 231130080231232383288251

theorem tailTrace_2025559 : CollatzResearch.WordTrace tailWord_2025559 prefixEnd_2025559 231130080231232383288251 := by
  unfold tailWord_2025559
  simp only [CollatzResearch.WordTrace]
  refine ⟨73878206068753155780783731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49252137379168770520522487 73878206068753155780783731)
  ·
    refine ⟨110817309103129733671175597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73878206068753155780783731 110817309103129733671175597)
    ·
      refine ⟨41556490913673650126690849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110817309103129733671175597 41556490913673650126690849)
      ·
        refine ⟨31167368185255237595018137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41556490913673650126690849 31167368185255237595018137)
        ·
          refine ⟨23375526138941428196263603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31167368185255237595018137 23375526138941428196263603)
          ·
            refine ⟨35063289208412142294395405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23375526138941428196263603 35063289208412142294395405)
            ·
              refine ⟨13148733453154553360398277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35063289208412142294395405 13148733453154553360398277)
              ·
                refine ⟨2465387522466478755074677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13148733453154553360398277 2465387522466478755074677)
                ·
                  refine ⟨231130080231232383288251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2465387522466478755074677 231130080231232383288251)
                  ·
                    rfl

theorem cell22_2025559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 5].length) (baseStart_2025559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025559 prefixEnd_2025559 := by exact prefixLift 2025559
  have htrace : WordTrace (prefixWord ++ tailWord_2025559) baseStart_2025559 baseEnd_2025559 := by
    simpa [prefixWord, tailWord_2025559, baseEnd_2025559] using wordTrace_append hprefix tailTrace_2025559
  have hstable : (prefixWord ++ tailWord_2025559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025559).length < 2 ^ (prefixWord ++ tailWord_2025559).sum := by decide
  have hdescent : baseEnd_2025559 < baseStart_2025559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025604 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 8]
def baseStart_2025604 : Nat := 118140960795 + 2025604 * 2 ^ 59
def prefixEnd_2025604 : Nat := 4983230072969 + 3 ^ 40 * 2025604 * 2
def baseEnd_2025604 : Nat := 231135215037777344163205

theorem tailTrace_2025604 : CollatzResearch.WordTrace tailWord_2025604 prefixEnd_2025604 231135215037777344163205 := by
  unfold tailWord_2025604
  simp only [CollatzResearch.WordTrace]
  refine ⟨36939923676795064233085933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49253231569060085644114577 36939923676795064233085933)
  ·
    refine ⟨13852471378798149087407225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36939923676795064233085933 13852471378798149087407225)
    ·
      refine ⟨10389353534098611815555419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13852471378798149087407225 10389353534098611815555419)
      ·
        refine ⟨15584030301147917723333129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10389353534098611815555419 15584030301147917723333129)
        ·
          refine ⟨11688022725860938292499847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15584030301147917723333129 11688022725860938292499847)
          ·
            refine ⟨17532034088791407438749771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11688022725860938292499847 17532034088791407438749771)
            ·
              refine ⟨26298051133187111158124657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17532034088791407438749771 26298051133187111158124657)
              ·
                refine ⟨19723538349890333368593493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26298051133187111158124657 19723538349890333368593493)
                ·
                  refine ⟨231135215037777344163205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19723538349890333368593493 231135215037777344163205)
                  ·
                    rfl

theorem cell22_2025604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_2025604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025604 prefixEnd_2025604 := by exact prefixLift 2025604
  have htrace : WordTrace (prefixWord ++ tailWord_2025604) baseStart_2025604 baseEnd_2025604 := by
    simpa [prefixWord, tailWord_2025604, baseEnd_2025604] using wordTrace_append hprefix tailTrace_2025604
  have hstable : (prefixWord ++ tailWord_2025604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025604).length < 2 ^ (prefixWord ++ tailWord_2025604).sum := by decide
  have hdescent : baseEnd_2025604 < baseStart_2025604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025621 : List Nat := [1, 3, 2, 1, 1, 1, 3, 6, 4]
def baseStart_2025621 : Nat := 118140960795 + 2025621 * 2 ^ 59
def prefixEnd_2025621 : Nat := 4983230072969 + 3 ^ 40 * 2025621 * 2
def baseEnd_2025621 : Nat := 231137154853583218271521

theorem tailTrace_2025621 : CollatzResearch.WordTrace tailWord_2025621 prefixEnd_2025621 231137154853583218271521 := by
  unfold tailWord_2025621
  simp only [CollatzResearch.WordTrace]
  refine ⟨73880467394528540369540717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49253644929685693579693811 73880467394528540369540717)
  ·
    refine ⟨27705175272948202638577769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73880467394528540369540717 27705175272948202638577769)
    ·
      refine ⟨20778881454711151978933327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27705175272948202638577769 20778881454711151978933327)
      ·
        refine ⟨31168322182066727968399991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20778881454711151978933327 31168322182066727968399991)
        ·
          refine ⟨46752483273100091952599987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31168322182066727968399991 46752483273100091952599987)
          ·
            refine ⟨70128724909650137928899981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46752483273100091952599987 70128724909650137928899981)
            ·
              refine ⟨26298271841118801723337493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70128724909650137928899981 26298271841118801723337493)
              ·
                refine ⟨1232731492552443830781445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26298271841118801723337493 1232731492552443830781445)
                ·
                  refine ⟨231137154853583218271521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1232731492552443830781445 231137154853583218271521)
                  ·
                    rfl

theorem cell22_2025621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_2025621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025621 prefixEnd_2025621 := by exact prefixLift 2025621
  have htrace : WordTrace (prefixWord ++ tailWord_2025621) baseStart_2025621 baseEnd_2025621 := by
    simpa [prefixWord, tailWord_2025621, baseEnd_2025621] using wordTrace_append hprefix tailTrace_2025621
  have hstable : (prefixWord ++ tailWord_2025621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025621).length < 2 ^ (prefixWord ++ tailWord_2025621).sum := by decide
  have hdescent : baseEnd_2025621 < baseStart_2025621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025668 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2025668 : Nat := 118140960795 + 2025668 * 2 ^ 59
def prefixEnd_2025668 : Nat := 4983230072969 + 3 ^ 40 * 2025668 * 2
def baseEnd_2025668 : Nat := 693427553621257198889419

theorem tailTrace_2025668 : CollatzResearch.WordTrace tailWord_2025668 prefixEnd_2025668 693427553621257198889419 := by
  unfold tailWord_2025668
  simp only [CollatzResearch.WordTrace]
  refine ⟨36941090812679133698250829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49254787750238844931001105 36941090812679133698250829)
  ·
    refine ⟨13852909054754675136844061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36941090812679133698250829 13852909054754675136844061)
    ·
      refine ⟨5194840895533003176316523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13852909054754675136844061 5194840895533003176316523)
      ·
        refine ⟨7792261343299504764474785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5194840895533003176316523 7792261343299504764474785)
        ·
          refine ⟨5844196007474628573356089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7792261343299504764474785 5844196007474628573356089)
          ·
            refine ⟨4383147005605971430017067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5844196007474628573356089 4383147005605971430017067)
            ·
              refine ⟨6574720508408957145025601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383147005605971430017067 6574720508408957145025601)
              ·
                refine ⟨4931040381306717858769201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6574720508408957145025601 4931040381306717858769201)
                ·
                  refine ⟨3698280285980038394076901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4931040381306717858769201 3698280285980038394076901)
                  ·
                    refine ⟨693427553621257198889419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3698280285980038394076901 693427553621257198889419)
                    ·
                      rfl

theorem cell22_2025668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2025668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025668 prefixEnd_2025668 := by exact prefixLift 2025668
  have htrace : WordTrace (prefixWord ++ tailWord_2025668) baseStart_2025668 baseEnd_2025668 := by
    simpa [prefixWord, tailWord_2025668, baseEnd_2025668] using wordTrace_append hprefix tailTrace_2025668
  have hstable : (prefixWord ++ tailWord_2025668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025668).length < 2 ^ (prefixWord ++ tailWord_2025668).sum := by decide
  have hdescent : baseEnd_2025668 < baseStart_2025668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025679 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 2, 6]
def baseStart_2025679 : Nat := 118140960795 + 2025679 * 2 ^ 59
def prefixEnd_2025679 : Nat := 4983230072969 + 3 ^ 40 * 2025679 * 2
def baseEnd_2025679 : Nat := 693431319146056836864385

theorem tailTrace_2025679 : CollatzResearch.WordTrace tailWord_2025679 prefixEnd_2025679 693431319146056836864385 := by
  unfold tailWord_2025679
  simp only [CollatzResearch.WordTrace]
  refine ⟨73882582828318416275152091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49255055218878944183434727 73882582828318416275152091)
  ·
    refine ⟨110823874242477624412728137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73882582828318416275152091 110823874242477624412728137)
    ·
      refine ⟨83117905681858218309546103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110823874242477624412728137 83117905681858218309546103)
      ·
        refine ⟨124676858522787327464319155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83117905681858218309546103 124676858522787327464319155)
        ·
          refine ⟨187015287784180991196478733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124676858522787327464319155 187015287784180991196478733)
          ·
            refine ⟨70130732919067871698679525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187015287784180991196478733 70130732919067871698679525)
            ·
              refine ⟨13149512422325225943502411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70130732919067871698679525 13149512422325225943502411)
              ·
                refine ⟨19724268633487838915253617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13149512422325225943502411 19724268633487838915253617)
                ·
                  refine ⟨14793201475115879186440213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19724268633487838915253617 14793201475115879186440213)
                  ·
                    refine ⟨693431319146056836864385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14793201475115879186440213 693431319146056836864385)
                    ·
                      rfl

theorem cell22_2025679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_2025679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025679 prefixEnd_2025679 := by exact prefixLift 2025679
  have htrace : WordTrace (prefixWord ++ tailWord_2025679) baseStart_2025679 baseEnd_2025679 := by
    simpa [prefixWord, tailWord_2025679, baseEnd_2025679] using wordTrace_append hprefix tailTrace_2025679
  have hstable : (prefixWord ++ tailWord_2025679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025679).length < 2 ^ (prefixWord ++ tailWord_2025679).sum := by decide
  have hdescent : baseEnd_2025679 < baseStart_2025679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025732 : List Nat := [2, 3, 2, 2, 3, 1, 1, 4, 1, 3]
def baseStart_2025732 : Nat := 118140960795 + 2025732 * 2 ^ 59
def prefixEnd_2025732 : Nat := 4983230072969 + 3 ^ 40 * 2025732 * 2
def baseEnd_2025732 : Nat := 693449462129182365289223

theorem tailTrace_2025732 : CollatzResearch.WordTrace tailWord_2025732 prefixEnd_2025732 693449462129182365289223 := by
  unfold tailWord_2025732
  simp only [CollatzResearch.WordTrace]
  refine ⟨36942257948563203163415725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49256343931417604217887633 36942257948563203163415725)
  ·
    refine ⟨13853346730711201186280897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36942257948563203163415725 13853346730711201186280897)
    ·
      refine ⟨10390010048033400889710673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13853346730711201186280897 10390010048033400889710673)
      ·
        refine ⟨7792507536025050667283005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10390010048033400889710673 7792507536025050667283005)
        ·
          refine ⟨2922190326009394000231127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7792507536025050667283005 2922190326009394000231127)
          ·
            refine ⟨4383285489014091000346691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922190326009394000231127 4383285489014091000346691)
            ·
              refine ⟨6574928233521136500520037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383285489014091000346691 6574928233521136500520037)
              ·
                refine ⟨1232799043785213093847507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6574928233521136500520037 1232799043785213093847507)
                ·
                  refine ⟨1849198565677819640771261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232799043785213093847507 1849198565677819640771261)
                  ·
                    refine ⟨693449462129182365289223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1849198565677819640771261 693449462129182365289223)
                    ·
                      rfl

theorem cell22_2025732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_2025732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025732 prefixEnd_2025732 := by exact prefixLift 2025732
  have htrace : WordTrace (prefixWord ++ tailWord_2025732) baseStart_2025732 baseEnd_2025732 := by
    simpa [prefixWord, tailWord_2025732, baseEnd_2025732] using wordTrace_append hprefix tailTrace_2025732
  have hstable : (prefixWord ++ tailWord_2025732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025732).length < 2 ^ (prefixWord ++ tailWord_2025732).sum := by decide
  have hdescent : baseEnd_2025732 < baseStart_2025732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025788 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 4, 3]
def baseStart_2025788 : Nat := 118140960795 + 2025788 * 2 ^ 59
def prefixEnd_2025788 : Nat := 4983230072969 + 3 ^ 40 * 2025788 * 2
def baseEnd_2025788 : Nat := 693468632073616885889051

theorem tailTrace_2025788 : CollatzResearch.WordTrace tailWord_2025788 prefixEnd_2025788 693468632073616885889051 := by
  unfold tailWord_2025788
  simp only [CollatzResearch.WordTrace]
  refine ⟨36943279192461763945435009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49257705589949018593913345 36943279192461763945435009)
  ·
    refine ⟨27707459394346322959076257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36943279192461763945435009 27707459394346322959076257)
    ·
      refine ⟨20780594545759742219307193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27707459394346322959076257 20780594545759742219307193)
      ·
        refine ⟨15585445909319806664480395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20780594545759742219307193 15585445909319806664480395)
        ·
          refine ⟨23378168863979709996720593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15585445909319806664480395 23378168863979709996720593)
          ·
            refine ⟨17533626647984782497540445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23378168863979709996720593 17533626647984782497540445)
            ·
              refine ⟨6575109992994293436577667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17533626647984782497540445 6575109992994293436577667)
              ·
                refine ⟨9862664989491440154866501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6575109992994293436577667 9862664989491440154866501)
                ·
                  refine ⟨1849249685529645029037469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9862664989491440154866501 1849249685529645029037469)
                  ·
                    refine ⟨693468632073616885889051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1849249685529645029037469 693468632073616885889051)
                    ·
                      rfl

theorem cell22_2025788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_2025788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025788 prefixEnd_2025788 := by exact prefixLift 2025788
  have htrace : WordTrace (prefixWord ++ tailWord_2025788) baseStart_2025788 baseEnd_2025788 := by
    simpa [prefixWord, tailWord_2025788, baseEnd_2025788] using wordTrace_append hprefix tailTrace_2025788
  have hstable : (prefixWord ++ tailWord_2025788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025788).length < 2 ^ (prefixWord ++ tailWord_2025788).sum := by decide
  have hdescent : baseEnd_2025788 < baseStart_2025788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025790 : List Nat := [4, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_2025790 : Nat := 118140960795 + 2025790 * 2 ^ 59
def prefixEnd_2025790 : Nat := 4983230072969 + 3 ^ 40 * 2025790 * 2
def baseEnd_2025790 : Nat := 231156438904829849113015

theorem tailTrace_2025790 : CollatzResearch.WordTrace tailWord_2025790 prefixEnd_2025790 231156438904829849113015 := by
  unfold tailWord_2025790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9235828916364535279055353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49257754220610854821628549 9235828916364535279055353)
  ·
    refine ⟨6926871687273401459291515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9235828916364535279055353 6926871687273401459291515)
    ·
      refine ⟨10390307530910102188937273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6926871687273401459291515 10390307530910102188937273)
      ·
        refine ⟨7792730648182576641702955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10390307530910102188937273 7792730648182576641702955)
        ·
          refine ⟨11689095972273864962554433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7792730648182576641702955 11689095972273864962554433)
          ·
            refine ⟨8766821979205398721915825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11689095972273864962554433 8766821979205398721915825)
            ·
              refine ⟨6575116484404049041436869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8766821979205398721915825 6575116484404049041436869)
              ·
                refine ⟨1232834340825759195269413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6575116484404049041436869 1232834340825759195269413)
                ·
                  refine ⟨231156438904829849113015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1232834340825759195269413 231156438904829849113015)
                  ·
                    rfl

theorem cell22_2025790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_2025790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025790 prefixEnd_2025790 := by exact prefixLift 2025790
  have htrace : WordTrace (prefixWord ++ tailWord_2025790) baseStart_2025790 baseEnd_2025790 := by
    simpa [prefixWord, tailWord_2025790, baseEnd_2025790] using wordTrace_append hprefix tailTrace_2025790
  have hstable : (prefixWord ++ tailWord_2025790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025790).length < 2 ^ (prefixWord ++ tailWord_2025790).sum := by decide
  have hdescent : baseEnd_2025790 < baseStart_2025790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025861 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_2025861 : Nat := 118140960795 + 2025861 * 2 ^ 59
def prefixEnd_2025861 : Nat := 4983230072969 + 3 ^ 40 * 2025861 * 2
def baseEnd_2025861 : Nat := 693493621465469028813827

theorem tailTrace_2025861 : CollatzResearch.WordTrace tailWord_2025861 prefixEnd_2025861 693493621465469028813827 := by
  unfold tailWord_2025861
  simp only [CollatzResearch.WordTrace]
  refine ⟨73889220913659061358277437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49259480609106040905518291 73889220913659061358277437)
  ·
    refine ⟨27708457842622148009354039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73889220913659061358277437 27708457842622148009354039)
    ·
      refine ⟨41562686763933222014031059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27708457842622148009354039 41562686763933222014031059)
      ·
        refine ⟨62344030145899833021046589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41562686763933222014031059 62344030145899833021046589)
        ·
          refine ⟨23379011304712437382892471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62344030145899833021046589 23379011304712437382892471)
          ·
            refine ⟨35068516957068656074338707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23379011304712437382892471 35068516957068656074338707)
            ·
              refine ⟨52602775435602984111508061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35068516957068656074338707 52602775435602984111508061)
              ·
                refine ⟨19726040788351119041815523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52602775435602984111508061 19726040788351119041815523)
                ·
                  refine ⟨29589061182526678562723285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19726040788351119041815523 29589061182526678562723285)
                  ·
                    refine ⟨693493621465469028813827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29589061182526678562723285 693493621465469028813827)
                    ·
                      rfl

theorem cell22_2025861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_2025861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025861 prefixEnd_2025861 := by exact prefixLift 2025861
  have htrace : WordTrace (prefixWord ++ tailWord_2025861) baseStart_2025861 baseEnd_2025861 := by
    simpa [prefixWord, tailWord_2025861, baseEnd_2025861] using wordTrace_append hprefix tailTrace_2025861
  have hstable : (prefixWord ++ tailWord_2025861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025861).length < 2 ^ (prefixWord ++ tailWord_2025861).sum := by decide
  have hdescent : baseEnd_2025861 < baseStart_2025861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025863 : List Nat := [1, 1, 4, 2, 2, 1, 3, 3, 5]
def baseStart_2025863 : Nat := 118140960795 + 2025863 * 2 ^ 59
def prefixEnd_2025863 : Nat := 4983230072969 + 3 ^ 40 * 2025863 * 2
def baseEnd_2025863 : Nat := 231164768702113896754607

theorem tailTrace_2025863 : CollatzResearch.WordTrace tailWord_2025863 prefixEnd_2025863 231164768702113896754607 := by
  unfold tailWord_2025863
  simp only [CollatzResearch.WordTrace]
  refine ⟨73889293859651815699850243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49259529239767877133233495 73889293859651815699850243)
  ·
    refine ⟨110833940789477723549775365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73889293859651815699850243 110833940789477723549775365)
    ·
      refine ⟨20781363898027073165582881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110833940789477723549775365 20781363898027073165582881)
      ·
        refine ⟨15586022923520304874187161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20781363898027073165582881 15586022923520304874187161)
        ·
          refine ⟨11689517192640228655640371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15586022923520304874187161 11689517192640228655640371)
          ·
            refine ⟨17534275788960342983460557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11689517192640228655640371 17534275788960342983460557)
            ·
              refine ⟨6575353420860128618797709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17534275788960342983460557 6575353420860128618797709)
              ·
                refine ⟨2465757532822548232049141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6575353420860128618797709 2465757532822548232049141)
                ·
                  refine ⟨231164768702113896754607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2465757532822548232049141 231164768702113896754607)
                  ·
                    rfl

theorem cell22_2025863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 5].length) (baseStart_2025863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025863 prefixEnd_2025863 := by exact prefixLift 2025863
  have htrace : WordTrace (prefixWord ++ tailWord_2025863) baseStart_2025863 baseEnd_2025863 := by
    simpa [prefixWord, tailWord_2025863, baseEnd_2025863] using wordTrace_append hprefix tailTrace_2025863
  have hstable : (prefixWord ++ tailWord_2025863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025863).length < 2 ^ (prefixWord ++ tailWord_2025863).sum := by decide
  have hdescent : baseEnd_2025863 < baseStart_2025863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025923 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 6, 3]
def baseStart_2025923 : Nat := 118140960795 + 2025923 * 2 ^ 59
def prefixEnd_2025923 : Nat := 4983230072969 + 3 ^ 40 * 2025923 * 2
def baseEnd_2025923 : Nat := 693514845332521533763637

theorem tailTrace_2025923 : CollatzResearch.WordTrace tailWord_2025923 prefixEnd_2025923 693514845332521533763637 := by
  unfold tailWord_2025923
  simp only [CollatzResearch.WordTrace]
  refine ⟨73891482239434445947034423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49260988159622963964689615 73891482239434445947034423)
  ·
    refine ⟨110837223359151668920551635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73891482239434445947034423 110837223359151668920551635)
    ·
      refine ⟨166255835038727503380827453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110837223359151668920551635 166255835038727503380827453)
      ·
        refine ⟨62345938139522813767810295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166255835038727503380827453 62345938139522813767810295)
        ·
          refine ⟨93518907209284220651715443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62345938139522813767810295 93518907209284220651715443)
          ·
            refine ⟨140278360813926330977573165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93518907209284220651715443 140278360813926330977573165)
            ·
              refine ⟨52604385305222374116589937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140278360813926330977573165 52604385305222374116589937)
              ·
                refine ⟨39453288978916780587442453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52604385305222374116589937 39453288978916780587442453)
                ·
                  refine ⟨1849372920886724090036365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39453288978916780587442453 1849372920886724090036365)
                  ·
                    refine ⟨693514845332521533763637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1849372920886724090036365 693514845332521533763637)
                    ·
                      rfl

theorem cell22_2025923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 3].length) (baseStart_2025923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025923 prefixEnd_2025923 := by exact prefixLift 2025923
  have htrace : WordTrace (prefixWord ++ tailWord_2025923) baseStart_2025923 baseEnd_2025923 := by
    simpa [prefixWord, tailWord_2025923, baseEnd_2025923] using wordTrace_append hprefix tailTrace_2025923
  have hstable : (prefixWord ++ tailWord_2025923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025923).length < 2 ^ (prefixWord ++ tailWord_2025923).sum := by decide
  have hdescent : baseEnd_2025923 < baseStart_2025923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025940 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_2025940 : Nat := 118140960795 + 2025940 * 2 ^ 59
def prefixEnd_2025940 : Nat := 4983230072969 + 3 ^ 40 * 2025940 * 2
def baseEnd_2025940 : Nat := 693520664779939156088585

theorem tailTrace_2025940 : CollatzResearch.WordTrace tailWord_2025940 prefixEnd_2025940 693520664779939156088585 := by
  unfold tailWord_2025940
  simp only [CollatzResearch.WordTrace]
  refine ⟨36946051140186428925201637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49261401520248571900268849 36946051140186428925201637)
  ·
    refine ⟨6927384588784955423475307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36946051140186428925201637 6927384588784955423475307)
    ·
      refine ⟨10391076883177433135212961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6927384588784955423475307 10391076883177433135212961)
      ·
        refine ⟨7793307662383074851409721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10391076883177433135212961 7793307662383074851409721)
        ·
          refine ⟨5844980746787306138557291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7793307662383074851409721 5844980746787306138557291)
          ·
            refine ⟨8767471120180959207835937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5844980746787306138557291 8767471120180959207835937)
            ·
              refine ⟨6575603340135719405876953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8767471120180959207835937 6575603340135719405876953)
              ·
                refine ⟨4931702505101789554407715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6575603340135719405876953 4931702505101789554407715)
                ·
                  refine ⟨7397553757652684331611573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4931702505101789554407715 7397553757652684331611573)
                  ·
                    refine ⟨693520664779939156088585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7397553757652684331611573 693520664779939156088585)
                    ·
                      rfl

theorem cell22_2025940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_2025940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025940 prefixEnd_2025940 := by exact prefixLift 2025940
  have htrace : WordTrace (prefixWord ++ tailWord_2025940) baseStart_2025940 baseEnd_2025940 := by
    simpa [prefixWord, tailWord_2025940, baseEnd_2025940] using wordTrace_append hprefix tailTrace_2025940
  have hstable : (prefixWord ++ tailWord_2025940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025940).length < 2 ^ (prefixWord ++ tailWord_2025940).sum := by decide
  have hdescent : baseEnd_2025940 < baseStart_2025940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025957 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 4, 3]
def baseStart_2025957 : Nat := 118140960795 + 2025957 * 2 ^ 59
def prefixEnd_2025957 : Nat := 4983230072969 + 3 ^ 40 * 2025957 * 2
def baseEnd_2025957 : Nat := 693526484227356778413533

theorem tailTrace_2025957 : CollatzResearch.WordTrace tailWord_2025957 prefixEnd_2025957 693526484227356778413533 := by
  unfold tailWord_2025957
  simp only [CollatzResearch.WordTrace]
  refine ⟨73892722321311269753772125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49261814880874179835848083 73892722321311269753772125)
  ·
    refine ⟨27709770870491726157664547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73892722321311269753772125 27709770870491726157664547)
    ·
      refine ⟨41564656305737589236496821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27709770870491726157664547 41564656305737589236496821)
      ·
        refine ⟨3896686528662898990921577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41564656305737589236496821 3896686528662898990921577)
        ·
          refine ⟨2922514896497174243191183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3896686528662898990921577 2922514896497174243191183)
          ·
            refine ⟨4383772344745761364786775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922514896497174243191183 4383772344745761364786775)
            ·
              refine ⟨6575658517118642047180163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383772344745761364786775 6575658517118642047180163)
              ·
                refine ⟨9863487775677963070770245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6575658517118642047180163 9863487775677963070770245)
                ·
                  refine ⟨1849403957939618075769421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9863487775677963070770245 1849403957939618075769421)
                  ·
                    refine ⟨693526484227356778413533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1849403957939618075769421 693526484227356778413533)
                    ·
                      rfl

theorem cell22_2025957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_2025957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025957 prefixEnd_2025957 := by exact prefixLift 2025957
  have htrace : WordTrace (prefixWord ++ tailWord_2025957) baseStart_2025957 baseEnd_2025957 := by
    simpa [prefixWord, tailWord_2025957, baseEnd_2025957] using wordTrace_append hprefix tailTrace_2025957
  have hstable : (prefixWord ++ tailWord_2025957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025957).length < 2 ^ (prefixWord ++ tailWord_2025957).sum := by decide
  have hdescent : baseEnd_2025957 < baseStart_2025957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025974 : List Nat := [5, 1, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_2025974 : Nat := 118140960795 + 2025974 * 2 ^ 59
def prefixEnd_2025974 : Nat := 4983230072969 + 3 ^ 40 * 2025974 * 2
def baseEnd_2025974 : Nat := 693532303674774400738481

theorem tailTrace_2025974 : CollatzResearch.WordTrace tailWord_2025974 prefixEnd_2025974 693532303674774400738481 := by
  unfold tailWord_2025974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4618333897640605103571311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49262228241499787771427317 4618333897640605103571311)
  ·
    refine ⟨6927500846460907655356967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4618333897640605103571311 6927500846460907655356967)
    ·
      refine ⟨10391251269691361483035451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6927500846460907655356967 10391251269691361483035451)
      ·
        refine ⟨15586876904537042224553177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10391251269691361483035451 15586876904537042224553177)
        ·
          refine ⟨11690157678402781668414883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15586876904537042224553177 11690157678402781668414883)
          ·
            refine ⟨17535236517604172502622325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11690157678402781668414883 17535236517604172502622325)
            ·
              refine ⟨1643928423525391172120843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17535236517604172502622325 1643928423525391172120843)
              ·
                refine ⟨2465892635288086758181265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643928423525391172120843 2465892635288086758181265)
                ·
                  refine ⟨1849419476466065068635949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2465892635288086758181265 1849419476466065068635949)
                  ·
                    refine ⟨693532303674774400738481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1849419476466065068635949 693532303674774400738481)
                    ·
                      rfl

theorem cell22_2025974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_2025974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2025974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2025974 prefixEnd_2025974 := by exact prefixLift 2025974
  have htrace : WordTrace (prefixWord ++ tailWord_2025974) baseStart_2025974 baseEnd_2025974 := by
    simpa [prefixWord, tailWord_2025974, baseEnd_2025974] using wordTrace_append hprefix tailTrace_2025974
  have hstable : (prefixWord ++ tailWord_2025974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025974).length < 2 ^ (prefixWord ++ tailWord_2025974).sum := by decide
  have hdescent : baseEnd_2025974 < baseStart_2025974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026073 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 5, 6]
def baseStart_2026073 : Nat := 118140960795 + 2026073 * 2 ^ 59
def prefixEnd_2026073 : Nat := 4983230072969 + 3 ^ 40 * 2026073 * 2
def baseEnd_2026073 : Nat := 693566193397971142513177

theorem tailTrace_2026073 : CollatzResearch.WordTrace tailWord_2026073 prefixEnd_2026073 693566193397971142513177 := by
  unfold tailWord_2026073
  simp only [CollatzResearch.WordTrace]
  refine ⟨73896953188891021564994873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49264635459260681043329915 73896953188891021564994873)
  ·
    refine ⟨55422714891668266173746155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73896953188891021564994873 55422714891668266173746155)
    ·
      refine ⟨83134072337502399260619233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55422714891668266173746155 83134072337502399260619233)
      ·
        refine ⟨62350554253126799445464425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83134072337502399260619233 62350554253126799445464425)
        ·
          refine ⟨46762915689845099584098319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62350554253126799445464425 46762915689845099584098319)
          ·
            refine ⟨70144373534767649376147479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46762915689845099584098319 70144373534767649376147479)
            ·
              refine ⟨105216560302151474064221219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70144373534767649376147479 105216560302151474064221219)
              ·
                refine ⟨157824840453227211096331829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105216560302151474064221219 157824840453227211096331829)
                ·
                  refine ⟨14796078792490051040281109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157824840453227211096331829 14796078792490051040281109)
                  ·
                    refine ⟨693566193397971142513177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14796078792490051040281109 693566193397971142513177)
                    ·
                      rfl

theorem cell22_2026073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_2026073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026073 prefixEnd_2026073 := by exact prefixLift 2026073
  have htrace : WordTrace (prefixWord ++ tailWord_2026073) baseStart_2026073 baseEnd_2026073 := by
    simpa [prefixWord, tailWord_2026073, baseEnd_2026073] using wordTrace_append hprefix tailTrace_2026073
  have hstable : (prefixWord ++ tailWord_2026073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026073).length < 2 ^ (prefixWord ++ tailWord_2026073).sum := by decide
  have hdescent : baseEnd_2026073 < baseStart_2026073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026090 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_2026090 : Nat := 118140960795 + 2026090 * 2 ^ 59
def prefixEnd_2026090 : Nat := 4983230072969 + 3 ^ 40 * 2026090 * 2
def baseEnd_2026090 : Nat := 693572012845388764838125

theorem tailTrace_2026090 : CollatzResearch.WordTrace tailWord_2026090 prefixEnd_2026090 693572012845388764838125 := by
  unfold tailWord_2026090
  simp only [CollatzResearch.WordTrace]
  refine ⟨18474393307457358367090931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49265048819886288978909149 18474393307457358367090931)
  ·
    refine ⟨27711589961186037550636397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18474393307457358367090931 27711589961186037550636397)
    ·
      refine ⟨10391846235444764081488649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27711589961186037550636397 10391846235444764081488649)
      ·
        refine ⟨7793884676583573061116487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10391846235444764081488649 7793884676583573061116487)
        ·
          refine ⟨11690827014875359591674731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7793884676583573061116487 11690827014875359591674731)
          ·
            refine ⟨17536240522313039387512097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11690827014875359591674731 17536240522313039387512097)
            ·
              refine ⟨13152180391734779540634073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17536240522313039387512097 13152180391734779540634073)
              ·
                refine ⟨9864135293801084655475555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13152180391734779540634073 9864135293801084655475555)
                ·
                  refine ⟨14796202940701626983213333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9864135293801084655475555 14796202940701626983213333)
                  ·
                    refine ⟨693572012845388764838125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14796202940701626983213333 693572012845388764838125)
                    ·
                      rfl

theorem cell22_2026090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_2026090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026090 prefixEnd_2026090 := by exact prefixLift 2026090
  have htrace : WordTrace (prefixWord ++ tailWord_2026090) baseStart_2026090 baseEnd_2026090 := by
    simpa [prefixWord, tailWord_2026090, baseEnd_2026090] using wordTrace_append hprefix tailTrace_2026090
  have hstable : (prefixWord ++ tailWord_2026090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026090).length < 2 ^ (prefixWord ++ tailWord_2026090).sum := by decide
  have hdescent : baseEnd_2026090 < baseStart_2026090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026092 : List Nat := [2, 2, 1, 1, 3, 1, 4, 3, 2, 3]
def baseStart_2026092 : Nat := 118140960795 + 2026092 * 2 ^ 59
def prefixEnd_2026092 : Nat := 4983230072969 + 3 ^ 40 * 2026092 * 2
def baseEnd_2026092 : Nat := 693572697486261426288119

theorem tailTrace_2026092 : CollatzResearch.WordTrace tailWord_2026092 prefixEnd_2026092 693572697486261426288119 := by
  unfold tailWord_2026092
  simp only [CollatzResearch.WordTrace]
  refine ⟨36948823087911093904968265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49265097450548125206624353 36948823087911093904968265)
  ·
    refine ⟨27711617315933320428726199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36948823087911093904968265 27711617315933320428726199)
    ·
      refine ⟨41567425973899980643089299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27711617315933320428726199 41567425973899980643089299)
      ·
        refine ⟨62351138960849970964633949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41567425973899980643089299 62351138960849970964633949)
        ·
          refine ⟨23381677110318739111737731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62351138960849970964633949 23381677110318739111737731)
          ·
            refine ⟨35072515665478108667606597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23381677110318739111737731 35072515665478108667606597)
            ·
              refine ⟨6576096687277145375176237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35072515665478108667606597 6576096687277145375176237)
              ·
                refine ⟨2466036257728929515691089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6576096687277145375176237 2466036257728929515691089)
                ·
                  refine ⟨1849527193296697136768317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2466036257728929515691089 1849527193296697136768317)
                  ·
                    refine ⟨693572697486261426288119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1849527193296697136768317 693572697486261426288119)
                    ·
                      rfl

theorem cell22_2026092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_2026092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026092 prefixEnd_2026092 := by exact prefixLift 2026092
  have htrace : WordTrace (prefixWord ++ tailWord_2026092) baseStart_2026092 baseEnd_2026092 := by
    simpa [prefixWord, tailWord_2026092, baseEnd_2026092] using wordTrace_append hprefix tailTrace_2026092
  have hstable : (prefixWord ++ tailWord_2026092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026092).length < 2 ^ (prefixWord ++ tailWord_2026092).sum := by decide
  have hdescent : baseEnd_2026092 < baseStart_2026092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026137 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 3, 3]
def baseStart_2026137 : Nat := 118140960795 + 2026137 * 2 ^ 59
def prefixEnd_2026137 : Nat := 4983230072969 + 3 ^ 40 * 2026137 * 2
def baseEnd_2026137 : Nat := 693588101905896308912981

theorem tailTrace_2026137 : CollatzResearch.WordTrace tailWord_2026137 prefixEnd_2026137 693588101905896308912981 := by
  unfold tailWord_2026137
  simp only [CollatzResearch.WordTrace]
  refine ⟨73899287460659160495324665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49266191640439440330216443 73899287460659160495324665)
  ·
    refine ⟨55424465595494370371493499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73899287460659160495324665 55424465595494370371493499)
    ·
      refine ⟨83136698393241555557240249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55424465595494370371493499 83136698393241555557240249)
      ·
        refine ⟨62352523794931166667930187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83136698393241555557240249 62352523794931166667930187)
        ·
          refine ⟨93528785692396750001895281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62352523794931166667930187 93528785692396750001895281)
          ·
            refine ⟨70146589269297562501421461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93528785692396750001895281 70146589269297562501421461)
            ·
              refine ⟨3288121371998323242254131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70146589269297562501421461 3288121371998323242254131)
              ·
                refine ⟨4932182057997484863381197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288121371998323242254131 4932182057997484863381197)
                ·
                  refine ⟨1849568271749056823767949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4932182057997484863381197 1849568271749056823767949)
                  ·
                    refine ⟨693588101905896308912981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1849568271749056823767949 693588101905896308912981)
                    ·
                      rfl

theorem cell22_2026137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 3].length) (baseStart_2026137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026137 prefixEnd_2026137 := by exact prefixLift 2026137
  have htrace : WordTrace (prefixWord ++ tailWord_2026137) baseStart_2026137 baseEnd_2026137 := by
    simpa [prefixWord, tailWord_2026137, baseEnd_2026137] using wordTrace_append hprefix tailTrace_2026137
  have hstable : (prefixWord ++ tailWord_2026137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026137).length < 2 ^ (prefixWord ++ tailWord_2026137).sum := by decide
  have hdescent : baseEnd_2026137 < baseStart_2026137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026188 : List Nat := [2, 2, 1, 5, 1, 2, 3, 2, 1, 3]
def baseStart_2026188 : Nat := 118140960795 + 2026188 * 2 ^ 59
def prefixEnd_2026188 : Nat := 4983230072969 + 3 ^ 40 * 2026188 * 2
def baseEnd_2026188 : Nat := 693605560248149175887825

theorem tailTrace_2026188 : CollatzResearch.WordTrace tailWord_2026188 prefixEnd_2026188 693605560248149175887825 := by
  unfold tailWord_2026188
  simp only [CollatzResearch.WordTrace]
  refine ⟨36950573791737198102715609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49267431722316264136954145 36950573791737198102715609)
  ·
    refine ⟨27712930343802898577036707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36950573791737198102715609 27712930343802898577036707)
    ·
      refine ⟨41569395515704347865555061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27712930343802898577036707 41569395515704347865555061)
      ·
        refine ⟨3897130829597282612395787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41569395515704347865555061 3897130829597282612395787)
        ·
          refine ⟨5845696244395923918593681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3897130829597282612395787 5845696244395923918593681)
          ·
            refine ⟨4384272183296942938945261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5845696244395923918593681 4384272183296942938945261)
            ·
              refine ⟨1644102068736353602104473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4384272183296942938945261 1644102068736353602104473)
              ·
                refine ⟨1233076551552265201578355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644102068736353602104473 1233076551552265201578355)
                ·
                  refine ⟨1849614827328397802367533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1233076551552265201578355 1849614827328397802367533)
                  ·
                    refine ⟨693605560248149175887825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1849614827328397802367533 693605560248149175887825)
                    ·
                      rfl

theorem cell22_2026188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_2026188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026188 prefixEnd_2026188 := by exact prefixLift 2026188
  have htrace : WordTrace (prefixWord ++ tailWord_2026188) baseStart_2026188 baseEnd_2026188 := by
    simpa [prefixWord, tailWord_2026188, baseEnd_2026188] using wordTrace_append hprefix tailTrace_2026188
  have hstable : (prefixWord ++ tailWord_2026188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026188).length < 2 ^ (prefixWord ++ tailWord_2026188).sum := by decide
  have hdescent : baseEnd_2026188 < baseStart_2026188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026274 : List Nat := [3, 3, 1, 1, 2, 3, 3, 6]
def baseStart_2026274 : Nat := 118140960795 + 2026274 * 2 ^ 59
def prefixEnd_2026274 : Nat := 4983230072969 + 3 ^ 40 * 2026274 * 2
def baseEnd_2026274 : Nat := 77070555533963735359729

theorem tailTrace_2026274 : CollatzResearch.WordTrace tailWord_2026274 prefixEnd_2026274 77070555533963735359729 := by
  unfold tailWord_2026274
  simp only [CollatzResearch.WordTrace]
  refine ⟨18476071065290708223265469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49269522840775221928707917 18476071065290708223265469)
  ·
    refine ⟨6928526649484015583724551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18476071065290708223265469 6928526649484015583724551)
    ·
      refine ⟨10392789974226023375586827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6928526649484015583724551 10392789974226023375586827)
      ·
        refine ⟨15589184961339035063380241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10392789974226023375586827 15589184961339035063380241)
        ·
          refine ⟨11691888721004276297535181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15589184961339035063380241 11691888721004276297535181)
          ·
            refine ⟨4384458270376603611575693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11691888721004276297535181 4384458270376603611575693)
            ·
              refine ⟨1644171851391226354340885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4384458270376603611575693 1644171851391226354340885)
              ·
                refine ⟨77070555533963735359729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1644171851391226354340885 77070555533963735359729)
                ·
                  rfl

theorem cell22_2026274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 6].length) (baseStart_2026274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026274 prefixEnd_2026274 := by exact prefixLift 2026274
  have htrace : WordTrace (prefixWord ++ tailWord_2026274) baseStart_2026274 baseEnd_2026274 := by
    simpa [prefixWord, tailWord_2026274, baseEnd_2026274] using wordTrace_append hprefix tailTrace_2026274
  have hstable : (prefixWord ++ tailWord_2026274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026274).length < 2 ^ (prefixWord ++ tailWord_2026274).sum := by decide
  have hdescent : baseEnd_2026274 < baseStart_2026274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026276 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_2026276 : Nat := 118140960795 + 2026276 * 2 ^ 59
def prefixEnd_2026276 : Nat := 4983230072969 + 3 ^ 40 * 2026276 * 2
def baseEnd_2026276 : Nat := 693635684446546279687555

theorem tailTrace_2026276 : CollatzResearch.WordTrace tailWord_2026276 prefixEnd_2026276 693635684446546279687555 := by
  unfold tailWord_2026276
  simp only [CollatzResearch.WordTrace]
  refine ⟨36952178603577793617317341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49269571471437058156423121 36952178603577793617317341)
  ·
    refine ⟨13857066976341672606494003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36952178603577793617317341 13857066976341672606494003)
    ·
      refine ⟨20785600464512508909741005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13857066976341672606494003 20785600464512508909741005)
      ·
        refine ⟨7794600174192190841152877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20785600464512508909741005 7794600174192190841152877)
        ·
          refine ⟨2922975065322071565432329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7794600174192190841152877 2922975065322071565432329)
          ·
            refine ⟨2192231298991553674074247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2922975065322071565432329 2192231298991553674074247)
            ·
              refine ⟨3288346948487330511111371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192231298991553674074247 3288346948487330511111371)
              ·
                refine ⟨4932520422730995766667057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288346948487330511111371 4932520422730995766667057)
                ·
                  refine ⟨3699390317048246825000293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4932520422730995766667057 3699390317048246825000293)
                  ·
                    refine ⟨693635684446546279687555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3699390317048246825000293 693635684446546279687555)
                    ·
                      rfl

theorem cell22_2026276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_2026276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026276 prefixEnd_2026276 := by exact prefixLift 2026276
  have htrace : WordTrace (prefixWord ++ tailWord_2026276) baseStart_2026276 baseEnd_2026276 := by
    simpa [prefixWord, tailWord_2026276, baseEnd_2026276] using wordTrace_append hprefix tailTrace_2026276
  have hstable : (prefixWord ++ tailWord_2026276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026276).length < 2 ^ (prefixWord ++ tailWord_2026276).sum := by decide
  have hdescent : baseEnd_2026276 < baseStart_2026276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026364 : List Nat := [2, 2, 2, 1, 1, 1, 1, 8, 4]
def baseStart_2026364 : Nat := 118140960795 + 2026364 * 2 ^ 59
def prefixEnd_2026364 : Nat := 4983230072969 + 3 ^ 40 * 2026364 * 2
def baseEnd_2026364 : Nat := 231221936214981127829095

theorem tailTrace_2026364 : CollatzResearch.WordTrace tailWord_2026364 prefixEnd_2026364 231221936214981127829095 := by
  unfold tailWord_2026364
  simp only [CollatzResearch.WordTrace]
  refine ⟨36953783415418389131919073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49271711220557852175892097 36953783415418389131919073)
  ·
    refine ⟨27715337561563791848939305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36953783415418389131919073 27715337561563791848939305)
    ·
      refine ⟨20786503171172843886704479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27715337561563791848939305 20786503171172843886704479)
      ·
        refine ⟨31179754756759265830056719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20786503171172843886704479 31179754756759265830056719)
        ·
          refine ⟨46769632135138898745085079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31179754756759265830056719 46769632135138898745085079)
          ·
            refine ⟨70154448202708348117627619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46769632135138898745085079 70154448202708348117627619)
            ·
              refine ⟨105231672304062522176441429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70154448202708348117627619 105231672304062522176441429)
              ·
                refine ⟨1233183659813232681755173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 105231672304062522176441429 1233183659813232681755173)
                ·
                  refine ⟨231221936214981127829095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1233183659813232681755173 231221936214981127829095)
                  ·
                    rfl

theorem cell22_2026364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_2026364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026364 prefixEnd_2026364 := by exact prefixLift 2026364
  have htrace : WordTrace (prefixWord ++ tailWord_2026364) baseStart_2026364 baseEnd_2026364 := by
    simpa [prefixWord, tailWord_2026364, baseEnd_2026364] using wordTrace_append hprefix tailTrace_2026364
  have hstable : (prefixWord ++ tailWord_2026364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026364).length < 2 ^ (prefixWord ++ tailWord_2026364).sum := by decide
  have hdescent : baseEnd_2026364 < baseStart_2026364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026396 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 1, 5]
def baseStart_2026396 : Nat := 118140960795 + 2026396 * 2 ^ 59
def prefixEnd_2026396 : Nat := 4983230072969 + 3 ^ 40 * 2026396 * 2
def baseEnd_2026396 : Nat := 693676762898905966687187

theorem tailTrace_2026396 : CollatzResearch.WordTrace tailWord_2026396 prefixEnd_2026396 693676762898905966687187 := by
  unfold tailWord_2026396
  simp only [CollatzResearch.WordTrace]
  refine ⟨36954366983360423864501521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49272489311147231819335361 36954366983360423864501521)
  ·
    refine ⟨27715775237520317898376141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36954366983360423864501521 27715775237520317898376141)
    ·
      refine ⟨10393415714070119211891053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27715775237520317898376141 10393415714070119211891053)
      ·
        refine ⟨3897530892776294704459145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10393415714070119211891053 3897530892776294704459145)
        ·
          refine ⟨2923148169582221028344359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3897530892776294704459145 2923148169582221028344359)
          ·
            refine ⟨4384722254373331542516539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923148169582221028344359 4384722254373331542516539)
            ·
              refine ⟨6577083381559997313774809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4384722254373331542516539 6577083381559997313774809)
              ·
                refine ⟨4932812536169997985331107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6577083381559997313774809 4932812536169997985331107)
                ·
                  refine ⟨7399218804254996977996661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4932812536169997985331107 7399218804254996977996661)
                  ·
                    refine ⟨693676762898905966687187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7399218804254996977996661 693676762898905966687187)
                    ·
                      rfl

theorem cell22_2026396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_2026396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026396 prefixEnd_2026396 := by exact prefixLift 2026396
  have htrace : WordTrace (prefixWord ++ tailWord_2026396) baseStart_2026396 baseEnd_2026396 := by
    simpa [prefixWord, tailWord_2026396, baseEnd_2026396] using wordTrace_append hprefix tailTrace_2026396
  have hstable : (prefixWord ++ tailWord_2026396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026396).length < 2 ^ (prefixWord ++ tailWord_2026396).sum := by decide
  have hdescent : baseEnd_2026396 < baseStart_2026396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026445 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2026445 : Nat := 118140960795 + 2026445 * 2 ^ 59
def prefixEnd_2026445 : Nat := 4983230072969 + 3 ^ 40 * 2026445 * 2
def baseEnd_2026445 : Nat := 693693536600286172212037

theorem tailTrace_2026445 : CollatzResearch.WordTrace tailWord_2026445 prefixEnd_2026445 693693536600286172212037 := by
  unfold tailWord_2026445
  simp only [CollatzResearch.WordTrace]
  refine ⟨73910521143543329097536789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49273680762362219398357859 73910521143543329097536789)
  ·
    refine ⟨3464555678603593551447037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73910521143543329097536789 3464555678603593551447037)
    ·
      refine ⟨1299208379476347581792639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3464555678603593551447037 1299208379476347581792639)
      ·
        refine ⟨1948812569214521372688959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299208379476347581792639 1948812569214521372688959)
        ·
          refine ⟨2923218853821782059033439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948812569214521372688959 2923218853821782059033439)
          ·
            refine ⟨4384828280732673088550159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923218853821782059033439 4384828280732673088550159)
            ·
              refine ⟨6577242421099009632825239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4384828280732673088550159 6577242421099009632825239)
              ·
                refine ⟨9865863631648514449237859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6577242421099009632825239 9865863631648514449237859)
                ·
                  refine ⟨14798795447472771673856789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9865863631648514449237859 14798795447472771673856789)
                  ·
                    refine ⟨693693536600286172212037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14798795447472771673856789 693693536600286172212037)
                    ·
                      rfl

theorem cell22_2026445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2026445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026445 prefixEnd_2026445 := by exact prefixLift 2026445
  have htrace : WordTrace (prefixWord ++ tailWord_2026445) baseStart_2026445 baseEnd_2026445 := by
    simpa [prefixWord, tailWord_2026445, baseEnd_2026445] using wordTrace_append hprefix tailTrace_2026445
  have hstable : (prefixWord ++ tailWord_2026445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026445).length < 2 ^ (prefixWord ++ tailWord_2026445).sum := by decide
  have hdescent : baseEnd_2026445 < baseStart_2026445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026458 : List Nat := [3, 1, 1, 2, 4, 1, 1, 5, 1, 3]
def baseStart_2026458 : Nat := 118140960795 + 2026458 * 2 ^ 59
def prefixEnd_2026458 : Nat := 4983230072969 + 3 ^ 40 * 2026458 * 2
def baseEnd_2026458 : Nat := 693697986765958471636997

theorem tailTrace_2026458 : CollatzResearch.WordTrace tailWord_2026458 prefixEnd_2026458 693697986765958471636997 := by
  unfold tailWord_2026458
  simp only [CollatzResearch.WordTrace]
  refine ⟨18477748823124058079440007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49273996861664154878506685 18477748823124058079440007)
  ·
    refine ⟨27716623234686087119160011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18477748823124058079440007 27716623234686087119160011)
    ·
      refine ⟨41574934852029130678740017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27716623234686087119160011 41574934852029130678740017)
      ·
        refine ⟨31181201139021848009055013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41574934852029130678740017 31181201139021848009055013)
        ·
          refine ⟨5846475213566596501697815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31181201139021848009055013 5846475213566596501697815)
          ·
            refine ⟨8769712820349894752546723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5846475213566596501697815 8769712820349894752546723)
            ·
              refine ⟨13154569230524842128820085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8769712820349894752546723 13154569230524842128820085)
              ·
                refine ⟨1233240865361703949576883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13154569230524842128820085 1233240865361703949576883)
                ·
                  refine ⟨1849861298042555924365325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1233240865361703949576883 1849861298042555924365325)
                  ·
                    refine ⟨693697986765958471636997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1849861298042555924365325 693697986765958471636997)
                    ·
                      rfl

theorem cell22_2026458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_2026458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026458 prefixEnd_2026458 := by exact prefixLift 2026458
  have htrace : WordTrace (prefixWord ++ tailWord_2026458) baseStart_2026458 baseEnd_2026458 := by
    simpa [prefixWord, tailWord_2026458, baseEnd_2026458] using wordTrace_append hprefix tailTrace_2026458
  have hstable : (prefixWord ++ tailWord_2026458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026458).length < 2 ^ (prefixWord ++ tailWord_2026458).sum := by decide
  have hdescent : baseEnd_2026458 < baseStart_2026458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026471 : List Nat := [1, 1, 5, 2, 2, 1, 3, 2, 5]
def baseStart_2026471 : Nat := 118140960795 + 2026471 * 2 ^ 59
def prefixEnd_2026471 : Nat := 4983230072969 + 3 ^ 40 * 2026471 * 2
def baseEnd_2026471 : Nat := 231234145643876923687319

theorem tailTrace_2026471 : CollatzResearch.WordTrace tailWord_2026471 prefixEnd_2026471 231234145643876923687319 := by
  unfold tailWord_2026471
  simp only [CollatzResearch.WordTrace]
  refine ⟨73911469441449135537983267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49274312960966090358655511 73911469441449135537983267)
  ·
    refine ⟨110867204162173703306974901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73911469441449135537983267 110867204162173703306974901)
    ·
      refine ⟨10393800390203784685028897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110867204162173703306974901 10393800390203784685028897)
      ·
        refine ⟨7795350292652838513771673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10393800390203784685028897 7795350292652838513771673)
        ·
          refine ⟨5846512719489628885328755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7795350292652838513771673 5846512719489628885328755)
          ·
            refine ⟨8769769079234443327993133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5846512719489628885328755 8769769079234443327993133)
            ·
              refine ⟨3288663404712916247997425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8769769079234443327993133 3288663404712916247997425)
              ·
                refine ⟨2466497553534687185998069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3288663404712916247997425 2466497553534687185998069)
                ·
                  refine ⟨231234145643876923687319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2466497553534687185998069 231234145643876923687319)
                  ·
                    rfl

theorem cell22_2026471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 5].length) (baseStart_2026471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026471 prefixEnd_2026471 := by exact prefixLift 2026471
  have htrace : WordTrace (prefixWord ++ tailWord_2026471) baseStart_2026471 baseEnd_2026471 := by
    simpa [prefixWord, tailWord_2026471, baseEnd_2026471] using wordTrace_append hprefix tailTrace_2026471
  have hstable : (prefixWord ++ tailWord_2026471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026471).length < 2 ^ (prefixWord ++ tailWord_2026471).sum := by decide
  have hdescent : baseEnd_2026471 < baseStart_2026471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026486 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_2026486 : Nat := 118140960795 + 2026486 * 2 ^ 59
def prefixEnd_2026486 : Nat := 4983230072969 + 3 ^ 40 * 2026486 * 2
def baseEnd_2026486 : Nat := 693707571738175731936911

theorem tailTrace_2026486 : CollatzResearch.WordTrace tailWord_2026486 prefixEnd_2026486 693707571738175731936911 := by
  unfold tailWord_2026486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4619501033524674568736207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49274677690929862066519541 4619501033524674568736207)
  ·
    refine ⟨6929251550287011853104311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4619501033524674568736207 6929251550287011853104311)
    ·
      refine ⟨10393877325430517779656467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6929251550287011853104311 10393877325430517779656467)
      ·
        refine ⟨15590815988145776669484701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10393877325430517779656467 15590815988145776669484701)
        ·
          refine ⟨5846555995554666251056763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15590815988145776669484701 5846555995554666251056763)
          ·
            refine ⟨8769833993331999376585145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5846555995554666251056763 8769833993331999376585145)
            ·
              refine ⟨6577375494998999532438859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8769833993331999376585145 6577375494998999532438859)
              ·
                refine ⟨9866063242498499298658289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6577375494998999532438859 9866063242498499298658289)
                ·
                  refine ⟨7399547431873874473993717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9866063242498499298658289 7399547431873874473993717)
                  ·
                    refine ⟨693707571738175731936911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7399547431873874473993717 693707571738175731936911)
                    ·
                      rfl

theorem cell22_2026486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_2026486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026486 prefixEnd_2026486 := by exact prefixLift 2026486
  have htrace : WordTrace (prefixWord ++ tailWord_2026486) baseStart_2026486 baseEnd_2026486 := by
    simpa [prefixWord, tailWord_2026486, baseEnd_2026486] using wordTrace_append hprefix tailTrace_2026486
  have hstable : (prefixWord ++ tailWord_2026486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026486).length < 2 ^ (prefixWord ++ tailWord_2026486).sum := by decide
  have hdescent : baseEnd_2026486 < baseStart_2026486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026501 : List Nat := [1, 3, 1, 1, 2, 3, 4, 2, 1, 4]
def baseStart_2026501 : Nat := 118140960795 + 2026501 * 2 ^ 59
def prefixEnd_2026501 : Nat := 4983230072969 + 3 ^ 40 * 2026501 * 2
def baseEnd_2026501 : Nat := 693712706544720692811865

theorem tailTrace_2026501 : CollatzResearch.WordTrace tailWord_2026501 prefixEnd_2026501 693712706544720692811865 := by
  unfold tailWord_2026501
  simp only [CollatzResearch.WordTrace]
  refine ⟨73912563631340450661575357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49275042420893633774383571 73912563631340450661575357)
  ·
    refine ⟨27717211361752668998090759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73912563631340450661575357 27717211361752668998090759)
    ·
      refine ⟨41575817042629003497136139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27717211361752668998090759 41575817042629003497136139)
      ·
        refine ⟨62363725563943505245704209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41575817042629003497136139 62363725563943505245704209)
        ·
          refine ⟨46772794172957628934278157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62363725563943505245704209 46772794172957628934278157)
          ·
            refine ⟨17539797814859110850354309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46772794172957628934278157 17539797814859110850354309)
            ·
              refine ⟨3288712090286083284441433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17539797814859110850354309 3288712090286083284441433)
              ·
                refine ⟨2466534067714562463331075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3288712090286083284441433 2466534067714562463331075)
                ·
                  refine ⟨3699801101571843694996613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466534067714562463331075 3699801101571843694996613)
                  ·
                    refine ⟨693712706544720692811865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3699801101571843694996613 693712706544720692811865)
                    ·
                      rfl

theorem cell22_2026501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_2026501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026501 prefixEnd_2026501 := by exact prefixLift 2026501
  have htrace : WordTrace (prefixWord ++ tailWord_2026501) baseStart_2026501 baseEnd_2026501 := by
    simpa [prefixWord, tailWord_2026501, baseEnd_2026501] using wordTrace_append hprefix tailTrace_2026501
  have hstable : (prefixWord ++ tailWord_2026501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026501).length < 2 ^ (prefixWord ++ tailWord_2026501).sum := by decide
  have hdescent : baseEnd_2026501 < baseStart_2026501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026531 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 4, 3]
def baseStart_2026531 : Nat := 118140960795 + 2026531 * 2 ^ 59
def prefixEnd_2026531 : Nat := 4983230072969 + 3 ^ 40 * 2026531 * 2
def baseEnd_2026531 : Nat := 693722976157810614561773

theorem tailTrace_2026531 : CollatzResearch.WordTrace tailWord_2026531 prefixEnd_2026531 693722976157810614561773 := by
  unfold tailWord_2026531
  simp only [CollatzResearch.WordTrace]
  refine ⟨73913657821231765785167447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49275771880821177190111631 73913657821231765785167447)
  ·
    refine ⟨110870486731847648677751171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73913657821231765785167447 110870486731847648677751171)
    ·
      refine ⟨166305730097771473016626757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110870486731847648677751171 166305730097771473016626757)
      ·
        refine ⟨31182324393332151190617517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166305730097771473016626757 31182324393332151190617517)
        ·
          refine ⟨11693371647499556696481569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31182324393332151190617517 11693371647499556696481569)
          ·
            refine ⟨8770028735624667522361177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11693371647499556696481569 8770028735624667522361177)
            ·
              refine ⟨6577521551718500641770883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8770028735624667522361177 6577521551718500641770883)
              ·
                refine ⟨9866282327577750962656325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6577521551718500641770883 9866282327577750962656325)
                ·
                  refine ⟨1849927936420828305498061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9866282327577750962656325 1849927936420828305498061)
                  ·
                    refine ⟨693722976157810614561773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1849927936420828305498061 693722976157810614561773)
                    ·
                      rfl

theorem cell22_2026531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 3].length) (baseStart_2026531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026531 prefixEnd_2026531 := by exact prefixLift 2026531
  have htrace : WordTrace (prefixWord ++ tailWord_2026531) baseStart_2026531 baseEnd_2026531 := by
    simpa [prefixWord, tailWord_2026531, baseEnd_2026531] using wordTrace_append hprefix tailTrace_2026531
  have hstable : (prefixWord ++ tailWord_2026531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026531).length < 2 ^ (prefixWord ++ tailWord_2026531).sum := by decide
  have hdescent : baseEnd_2026531 < baseStart_2026531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026533 : List Nat := [1, 3, 1, 2, 2, 2, 5, 2, 4]
def baseStart_2026533 : Nat := 118140960795 + 2026533 * 2 ^ 59
def prefixEnd_2026533 : Nat := 4983230072969 + 3 ^ 40 * 2026533 * 2
def baseEnd_2026533 : Nat := 231241220266227758670589

theorem tailTrace_2026533 : CollatzResearch.WordTrace tailWord_2026533 prefixEnd_2026533 231241220266227758670589 := by
  unfold tailWord_2026533
  simp only [CollatzResearch.WordTrace]
  refine ⟨73913730767224520126740253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49275820511483013417826835 73913730767224520126740253)
  ·
    refine ⟨27717649037709195047527595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73913730767224520126740253 27717649037709195047527595)
    ·
      refine ⟨41576473556563792571291393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27717649037709195047527595 41576473556563792571291393)
      ·
        refine ⟨31182355167422844428468545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41576473556563792571291393 31182355167422844428468545)
        ·
          refine ⟨23386766375567133321351409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31182355167422844428468545 23386766375567133321351409)
          ·
            refine ⟨17540074781675349991013557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23386766375567133321351409 17540074781675349991013557)
            ·
              refine ⟨1644382010782064061657521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17540074781675349991013557 1644382010782064061657521)
              ·
                refine ⟨1233286508086548046243141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644382010782064061657521 1233286508086548046243141)
                ·
                  refine ⟨231241220266227758670589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1233286508086548046243141 231241220266227758670589)
                  ·
                    rfl

theorem cell22_2026533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_2026533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026533 prefixEnd_2026533 := by exact prefixLift 2026533
  have htrace : WordTrace (prefixWord ++ tailWord_2026533) baseStart_2026533 baseEnd_2026533 := by
    simpa [prefixWord, tailWord_2026533, baseEnd_2026533] using wordTrace_append hprefix tailTrace_2026533
  have hstable : (prefixWord ++ tailWord_2026533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026533).length < 2 ^ (prefixWord ++ tailWord_2026533).sum := by decide
  have hdescent : baseEnd_2026533 < baseStart_2026533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026544 : List Nat := [2, 1, 1, 1, 2, 4, 4, 7]
def baseStart_2026544 : Nat := 118140960795 + 2026544 * 2 ^ 59
def prefixEnd_2026544 : Nat := 4983230072969 + 3 ^ 40 * 2026544 * 2
def baseEnd_2026544 : Nat := 77080825147053657109637

theorem tailTrace_2026544 : CollatzResearch.WordTrace tailWord_2026544 prefixEnd_2026544 77080825147053657109637 := by
  unfold tailWord_2026544
  simp only [CollatzResearch.WordTrace]
  refine ⟨36957065985092334502695343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49276087980123112670260457 36957065985092334502695343)
  ·
    refine ⟨55435598977638501754043015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36957065985092334502695343 55435598977638501754043015)
    ·
      refine ⟨83153398466457752631064523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55435598977638501754043015 83153398466457752631064523)
      ·
        refine ⟨124730097699686628946596785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83153398466457752631064523 124730097699686628946596785)
        ·
          refine ⟨93547573274764971709947589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124730097699686628946596785 93547573274764971709947589)
          ·
            refine ⟨17540169989018432195615173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93547573274764971709947589 17540169989018432195615173)
            ·
              refine ⟨3288781872940956036677845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17540169989018432195615173 3288781872940956036677845)
              ·
                refine ⟨77080825147053657109637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3288781872940956036677845 77080825147053657109637)
                ·
                  rfl

theorem cell22_2026544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 7].length) (baseStart_2026544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026544 prefixEnd_2026544 := by exact prefixLift 2026544
  have htrace : WordTrace (prefixWord ++ tailWord_2026544) baseStart_2026544 baseEnd_2026544 := by
    simpa [prefixWord, tailWord_2026544, baseEnd_2026544] using wordTrace_append hprefix tailTrace_2026544
  have hstable : (prefixWord ++ tailWord_2026544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026544).length < 2 ^ (prefixWord ++ tailWord_2026544).sum := by decide
  have hdescent : baseEnd_2026544 < baseStart_2026544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026649 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 2, 9]
def baseStart_2026649 : Nat := 118140960795 + 2026649 * 2 ^ 59
def prefixEnd_2026649 : Nat := 4983230072969 + 3 ^ 40 * 2026649 * 2
def baseEnd_2026649 : Nat := 693763369969297640111411

theorem tailTrace_2026649 : CollatzResearch.WordTrace tailWord_2026649 prefixEnd_2026649 693763369969297640111411 := by
  unfold tailWord_2026649
  simp only [CollatzResearch.WordTrace]
  refine ⟨73917961634804271937963001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49278641089869514625308667 73917961634804271937963001)
  ·
    refine ⟨55438471226103203953472251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73917961634804271937963001 55438471226103203953472251)
    ·
      refine ⟨83157706839154805930208377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55438471226103203953472251 83157706839154805930208377)
      ·
        refine ⟨62368280129366104447656283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83157706839154805930208377 62368280129366104447656283)
        ·
          refine ⟨93552420194049156671484425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62368280129366104447656283 93552420194049156671484425)
          ·
            refine ⟨70164315145536867503613319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93552420194049156671484425 70164315145536867503613319)
            ·
              refine ⟨105246472718305301255419979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70164315145536867503613319 105246472718305301255419979)
              ·
                refine ⟨157869709077457951883129969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105246472718305301255419979 157869709077457951883129969)
                ·
                  refine ⟨118402281808093463912347477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157869709077457951883129969 118402281808093463912347477)
                  ·
                    refine ⟨693763369969297640111411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 118402281808093463912347477 693763369969297640111411)
                    ·
                      rfl

theorem cell22_2026649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_2026649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026649 prefixEnd_2026649 := by exact prefixLift 2026649
  have htrace : WordTrace (prefixWord ++ tailWord_2026649) baseStart_2026649 baseEnd_2026649 := by
    simpa [prefixWord, tailWord_2026649, baseEnd_2026649] using wordTrace_append hprefix tailTrace_2026649
  have hstable : (prefixWord ++ tailWord_2026649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026649).length < 2 ^ (prefixWord ++ tailWord_2026649).sum := by decide
  have hdescent : baseEnd_2026649 < baseStart_2026649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026678 : List Nat := [5, 1, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_2026678 : Nat := 118140960795 + 2026678 * 2 ^ 59
def prefixEnd_2026678 : Nat := 4983230072969 + 3 ^ 40 * 2026678 * 2
def baseEnd_2026678 : Nat := 693773297261951231136323

theorem tailTrace_2026678 : CollatzResearch.WordTrace tailWord_2026678 prefixEnd_2026678 693773297261951231136323 := by
  unfold tailWord_2026678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4619938709481200618173043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49279346234466139927179125 4619938709481200618173043)
  ·
    refine ⟨6929908064221800927259565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4619938709481200618173043 6929908064221800927259565)
    ·
      refine ⟨2598715524083175347722337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6929908064221800927259565 2598715524083175347722337)
      ·
        refine ⟨1949036643062381510791753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2598715524083175347722337 1949036643062381510791753)
        ·
          refine ⟨1461777482296786133093815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1949036643062381510791753 1461777482296786133093815)
          ·
            refine ⟨2192666223445179199640723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461777482296786133093815 2192666223445179199640723)
            ·
              refine ⟨3288999335167768799461085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192666223445179199640723 3288999335167768799461085)
              ·
                refine ⟨1233374750687913299797907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3288999335167768799461085 1233374750687913299797907)
                ·
                  refine ⟨1850062126031869949696861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1233374750687913299797907 1850062126031869949696861)
                  ·
                    refine ⟨693773297261951231136323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1850062126031869949696861 693773297261951231136323)
                    ·
                      rfl

theorem cell22_2026678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_2026678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026678 prefixEnd_2026678 := by exact prefixLift 2026678
  have htrace : WordTrace (prefixWord ++ tailWord_2026678) baseStart_2026678 baseEnd_2026678 := by
    simpa [prefixWord, tailWord_2026678, baseEnd_2026678] using wordTrace_append hprefix tailTrace_2026678
  have hstable : (prefixWord ++ tailWord_2026678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026678).length < 2 ^ (prefixWord ++ tailWord_2026678).sum := by decide
  have hdescent : baseEnd_2026678 < baseStart_2026678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026681 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 1, 6]
def baseStart_2026681 : Nat := 118140960795 + 2026681 * 2 ^ 59
def prefixEnd_2026681 : Nat := 4983230072969 + 3 ^ 40 * 2026681 * 2
def baseEnd_2026681 : Nat := 693774324223260223311313

theorem tailTrace_2026681 : CollatzResearch.WordTrace tailWord_2026681 prefixEnd_2026681 693774324223260223311313 := by
  unfold tailWord_2026681
  simp only [CollatzResearch.WordTrace]
  refine ⟨73919128770688341403127897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49279419180458894268751931 73919128770688341403127897)
  ·
    refine ⟨55439346578016256052345923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73919128770688341403127897 55439346578016256052345923)
    ·
      refine ⟨83159019867024384078518885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55439346578016256052345923 83159019867024384078518885)
      ·
        refine ⟨15592316225067072014722291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83159019867024384078518885 15592316225067072014722291)
        ·
          refine ⟨23388474337600608022083437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15592316225067072014722291 23388474337600608022083437)
          ·
            refine ⟨8770677876600228008281289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23388474337600608022083437 8770677876600228008281289)
            ·
              refine ⟨6578008407450171006210967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8770677876600228008281289 6578008407450171006210967)
              ·
                refine ⟨9867012611175256509316451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6578008407450171006210967 9867012611175256509316451)
                ·
                  refine ⟨14800518916762884763974677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9867012611175256509316451 14800518916762884763974677)
                  ·
                    refine ⟨693774324223260223311313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14800518916762884763974677 693774324223260223311313)
                    ·
                      rfl

theorem cell22_2026681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_2026681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026681 prefixEnd_2026681 := by exact prefixLift 2026681
  have htrace : WordTrace (prefixWord ++ tailWord_2026681) baseStart_2026681 baseEnd_2026681 := by
    simpa [prefixWord, tailWord_2026681, baseEnd_2026681] using wordTrace_append hprefix tailTrace_2026681
  have hstable : (prefixWord ++ tailWord_2026681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026681).length < 2 ^ (prefixWord ++ tailWord_2026681).sum := by decide
  have hdescent : baseEnd_2026681 < baseStart_2026681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026698 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_2026698 : Nat := 118140960795 + 2026698 * 2 ^ 59
def prefixEnd_2026698 : Nat := 4983230072969 + 3 ^ 40 * 2026698 * 2
def baseEnd_2026698 : Nat := 693780143670677845636261

theorem tailTrace_2026698 : CollatzResearch.WordTrace tailWord_2026698 prefixEnd_2026698 693780143670677845636261 := by
  unfold tailWord_2026698
  simp only [CollatzResearch.WordTrace]
  refine ⟨18479937202906688326624187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49279832541084502204331165 18479937202906688326624187)
  ·
    refine ⟨27719905804360032489936281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18479937202906688326624187 27719905804360032489936281)
    ·
      refine ⟨20789929353270024367452211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27719905804360032489936281 20789929353270024367452211)
      ·
        refine ⟨31184894029905036551178317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20789929353270024367452211 31184894029905036551178317)
        ·
          refine ⟨11694335261214388706691869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31184894029905036551178317 11694335261214388706691869)
          ·
            refine ⟨4385375722955395765009451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11694335261214388706691869 4385375722955395765009451)
            ·
              refine ⟨6578063584433093647514177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385375722955395765009451 6578063584433093647514177)
              ·
                refine ⟨4933547688324820235635633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6578063584433093647514177 4933547688324820235635633)
                ·
                  refine ⟨3700160766243615176726725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4933547688324820235635633 3700160766243615176726725)
                  ·
                    refine ⟨693780143670677845636261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3700160766243615176726725 693780143670677845636261)
                    ·
                      rfl

theorem cell22_2026698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_2026698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026698 prefixEnd_2026698 := by exact prefixLift 2026698
  have htrace : WordTrace (prefixWord ++ tailWord_2026698) baseStart_2026698 baseEnd_2026698 := by
    simpa [prefixWord, tailWord_2026698, baseEnd_2026698] using wordTrace_append hprefix tailTrace_2026698
  have hstable : (prefixWord ++ tailWord_2026698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026698).length < 2 ^ (prefixWord ++ tailWord_2026698).sum := by decide
  have hdescent : baseEnd_2026698 < baseStart_2026698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026702 : List Nat := [4, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_2026702 : Nat := 118140960795 + 2026702 * 2 ^ 59
def prefixEnd_2026702 : Nat := 4983230072969 + 3 ^ 40 * 2026702 * 2
def baseEnd_2026702 : Nat := 231260504317474389512083

theorem tailTrace_2026702 : CollatzResearch.WordTrace tailWord_2026702 prefixEnd_2026702 231260504317474389512083 := by
  unfold tailWord_2026702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9239986837951532748705295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49279929802408174659761573 9239986837951532748705295)
  ·
    refine ⟨13859980256927299123057943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9239986837951532748705295 13859980256927299123057943)
    ·
      refine ⟨20789970385390948684586915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13859980256927299123057943 20789970385390948684586915)
      ·
        refine ⟨31184955578086423026880373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20789970385390948684586915 31184955578086423026880373)
        ·
          refine ⟨2923589585445602158770035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31184955578086423026880373 2923589585445602158770035)
          ·
            refine ⟨4385384378168403238155053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923589585445602158770035 4385384378168403238155053)
            ·
              refine ⟨1644519141813151214308145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4385384378168403238155053 1644519141813151214308145)
              ·
                refine ⟨1233389356359863410731109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644519141813151214308145 1233389356359863410731109)
                ·
                  refine ⟨231260504317474389512083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1233389356359863410731109 231260504317474389512083)
                  ·
                    rfl

theorem cell22_2026702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_2026702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026702 prefixEnd_2026702 := by exact prefixLift 2026702
  have htrace : WordTrace (prefixWord ++ tailWord_2026702) baseStart_2026702 baseEnd_2026702 := by
    simpa [prefixWord, tailWord_2026702, baseEnd_2026702] using wordTrace_append hprefix tailTrace_2026702
  have hstable : (prefixWord ++ tailWord_2026702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026702).length < 2 ^ (prefixWord ++ tailWord_2026702).sum := by decide
  have hdescent : baseEnd_2026702 < baseStart_2026702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026717 : List Nat := [1, 4, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_2026717 : Nat := 118140960795 + 2026717 * 2 ^ 59
def prefixEnd_2026717 : Nat := 4983230072969 + 3 ^ 40 * 2026717 * 2
def baseEnd_2026717 : Nat := 693786647758968129411203

theorem tailTrace_2026717 : CollatzResearch.WordTrace tailWord_2026717 prefixEnd_2026717 693786647758968129411203 := by
  unfold tailWord_2026717
  simp only [CollatzResearch.WordTrace]
  refine ⟨73920441798557919551438405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49280294532371946367625603 73920441798557919551438405)
  ·
    refine ⟨13860082837229609915894701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73920441798557919551438405 13860082837229609915894701)
    ·
      refine ⟨5197531063961103718460513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13860082837229609915894701 5197531063961103718460513)
      ·
        refine ⟨3898148297970827788845385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5197531063961103718460513 3898148297970827788845385)
        ·
          refine ⟨2923611223478120841634039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3898148297970827788845385 2923611223478120841634039)
          ·
            refine ⟨4385416835217181262451059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923611223478120841634039 4385416835217181262451059)
            ·
              refine ⟨6578125252825771893676589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385416835217181262451059 6578125252825771893676589)
              ·
                refine ⟨2466796969809664460128721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6578125252825771893676589 2466796969809664460128721)
                ·
                  refine ⟨1850097727357248345096541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2466796969809664460128721 1850097727357248345096541)
                  ·
                    refine ⟨693786647758968129411203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1850097727357248345096541 693786647758968129411203)
                    ·
                      rfl

theorem cell22_2026717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_2026717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026717 prefixEnd_2026717 := by exact prefixLift 2026717
  have htrace : WordTrace (prefixWord ++ tailWord_2026717) baseStart_2026717 baseEnd_2026717 := by
    simpa [prefixWord, tailWord_2026717, baseEnd_2026717] using wordTrace_append hprefix tailTrace_2026717
  have hstable : (prefixWord ++ tailWord_2026717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026717).length < 2 ^ (prefixWord ++ tailWord_2026717).sum := by decide
  have hdescent : baseEnd_2026717 < baseStart_2026717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026728 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 5, 3]
def baseStart_2026728 : Nat := 118140960795 + 2026728 * 2 ^ 59
def prefixEnd_2026728 : Nat := 4983230072969 + 3 ^ 40 * 2026728 * 2
def baseEnd_2026728 : Nat := 693790413283767767386169

theorem tailTrace_2026728 : CollatzResearch.WordTrace tailWord_2026728 prefixEnd_2026728 693790413283767767386169 := by
  unfold tailWord_2026728
  simp only [CollatzResearch.WordTrace]
  refine ⟨36960421500759034215044419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49280562001012045620059225 36960421500759034215044419)
  ·
    refine ⟨55440632251138551322566629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36960421500759034215044419 55440632251138551322566629)
    ·
      refine ⟨10395118547088478372981243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55440632251138551322566629 10395118547088478372981243)
      ·
        refine ⟨15592677820632717559471865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10395118547088478372981243 15592677820632717559471865)
        ·
          refine ⟨11694508365474538169603899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15592677820632717559471865 11694508365474538169603899)
          ·
            refine ⟨17541762548211807254405849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11694508365474538169603899 17541762548211807254405849)
            ·
              refine ⟨13156321911158855440804387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17541762548211807254405849 13156321911158855440804387)
              ·
                refine ⟨19734482866738283161206581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13156321911158855440804387 19734482866738283161206581)
                ·
                  refine ⟨1850107768756714046363117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19734482866738283161206581 1850107768756714046363117)
                  ·
                    refine ⟨693790413283767767386169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1850107768756714046363117 693790413283767767386169)
                    ·
                      rfl

theorem cell22_2026728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_2026728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026728 prefixEnd_2026728 := by exact prefixLift 2026728
  have htrace : WordTrace (prefixWord ++ tailWord_2026728) baseStart_2026728 baseEnd_2026728 := by
    simpa [prefixWord, tailWord_2026728, baseEnd_2026728] using wordTrace_append hprefix tailTrace_2026728
  have hstable : (prefixWord ++ tailWord_2026728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026728).length < 2 ^ (prefixWord ++ tailWord_2026728).sum := by decide
  have hdescent : baseEnd_2026728 < baseStart_2026728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026745 : List Nat := [1, 2, 1, 3, 1, 1, 4, 5, 1, 3]
def baseStart_2026745 : Nat := 118140960795 + 2026745 * 2 ^ 59
def prefixEnd_2026745 : Nat := 4983230072969 + 3 ^ 40 * 2026745 * 2
def baseEnd_2026745 : Nat := 693796232731185389711117

theorem tailTrace_2026745 : CollatzResearch.WordTrace tailWord_2026745 prefixEnd_2026745 693796232731185389711117 := by
  unfold tailWord_2026745
  simp only [CollatzResearch.WordTrace]
  refine ⟨73921463042456480333457689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49280975361637653555638459 73921463042456480333457689)
  ·
    refine ⟨55441097281842360250093267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73921463042456480333457689 55441097281842360250093267)
    ·
      refine ⟨83161645922763540375139901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55441097281842360250093267 83161645922763540375139901)
      ·
        refine ⟨31185617221036327640677463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83161645922763540375139901 31185617221036327640677463)
        ·
          refine ⟨46778425831554491461016195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31185617221036327640677463 46778425831554491461016195)
          ·
            refine ⟨70167638747331737191524293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46778425831554491461016195 70167638747331737191524293)
            ·
              refine ⟨13156432265124700723410805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70167638747331737191524293 13156432265124700723410805)
              ·
                refine ⟨1233415524855440692819763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13156432265124700723410805 1233415524855440692819763)
                ·
                  refine ⟨1850123287283161039229645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1233415524855440692819763 1850123287283161039229645)
                  ·
                    refine ⟨693796232731185389711117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1850123287283161039229645 693796232731185389711117)
                    ·
                      rfl

theorem cell22_2026745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 1, 3].length) (baseStart_2026745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026745 prefixEnd_2026745 := by exact prefixLift 2026745
  have htrace : WordTrace (prefixWord ++ tailWord_2026745) baseStart_2026745 baseEnd_2026745 := by
    simpa [prefixWord, tailWord_2026745, baseEnd_2026745] using wordTrace_append hprefix tailTrace_2026745
  have hstable : (prefixWord ++ tailWord_2026745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026745).length < 2 ^ (prefixWord ++ tailWord_2026745).sum := by decide
  have hdescent : baseEnd_2026745 < baseStart_2026745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026788 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_2026788 : Nat := 118140960795 + 2026788 * 2 ^ 59
def prefixEnd_2026788 : Nat := 4983230072969 + 3 ^ 40 * 2026788 * 2
def baseEnd_2026788 : Nat := 693810952509947610885985

theorem tailTrace_2026788 : CollatzResearch.WordTrace tailWord_2026788 prefixEnd_2026788 693810952509947610885985 := by
  unfold tailWord_2026788
  simp only [CollatzResearch.WordTrace]
  refine ⟨36961515690650349338636509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49282020920867132451515345 36961515690650349338636509)
  ·
    refine ⟨13860568383993881001988691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36961515690650349338636509 13860568383993881001988691)
    ·
      refine ⟨20790852575990821502983037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13860568383993881001988691 20790852575990821502983037)
      ·
        refine ⟨7796569715996558063618639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20790852575990821502983037 7796569715996558063618639)
        ·
          refine ⟨11694854573994837095427959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7796569715996558063618639 11694854573994837095427959)
          ·
            refine ⟨17542281860992255643141939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11694854573994837095427959 17542281860992255643141939)
            ·
              refine ⟨26313422791488383464712909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17542281860992255643141939 26313422791488383464712909)
              ·
                refine ⟨9867533546808143799267341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26313422791488383464712909 9867533546808143799267341)
                ·
                  refine ⟨3700325080053053924725253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9867533546808143799267341 3700325080053053924725253)
                  ·
                    refine ⟨693810952509947610885985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3700325080053053924725253 693810952509947610885985)
                    ·
                      rfl

theorem cell22_2026788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_2026788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026788 prefixEnd_2026788 := by exact prefixLift 2026788
  have htrace : WordTrace (prefixWord ++ tailWord_2026788) baseStart_2026788 baseEnd_2026788 := by
    simpa [prefixWord, tailWord_2026788, baseEnd_2026788] using wordTrace_append hprefix tailTrace_2026788
  have hstable : (prefixWord ++ tailWord_2026788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026788).length < 2 ^ (prefixWord ++ tailWord_2026788).sum := by decide
  have hdescent : baseEnd_2026788 < baseStart_2026788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026805 : List Nat := [1, 3, 3, 1, 2, 3, 1, 3, 1, 4]
def baseStart_2026805 : Nat := 118140960795 + 2026805 * 2 ^ 59
def prefixEnd_2026805 : Nat := 4983230072969 + 3 ^ 40 * 2026805 * 2
def baseEnd_2026805 : Nat := 693816771957365233210933

theorem tailTrace_2026805 : CollatzResearch.WordTrace tailWord_2026805 prefixEnd_2026805 693816771957365233210933 := by
  unfold tailWord_2026805
  simp only [CollatzResearch.WordTrace]
  refine ⟨73923651422239110580641869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49282434281492740387094579 73923651422239110580641869)
  ·
    refine ⟨27721369283339666467740701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73923651422239110580641869 27721369283339666467740701)
    ·
      refine ⟨10395513481252374925402763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27721369283339666467740701 10395513481252374925402763)
      ·
        refine ⟨15593270221878562388104145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10395513481252374925402763 15593270221878562388104145)
        ·
          refine ⟨11694952666408921791078109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15593270221878562388104145 11694952666408921791078109)
          ·
            refine ⟨4385607249903345671654291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11694952666408921791078109 4385607249903345671654291)
            ·
              refine ⟨6578410874855018507481437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385607249903345671654291 6578410874855018507481437)
              ·
                refine ⟨2466904078070631940305539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6578410874855018507481437 2466904078070631940305539)
                ·
                  refine ⟨3700356117105947910458309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466904078070631940305539 3700356117105947910458309)
                  ·
                    refine ⟨693816771957365233210933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3700356117105947910458309 693816771957365233210933)
                    ·
                      rfl

theorem cell22_2026805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_2026805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026805 prefixEnd_2026805 := by exact prefixLift 2026805
  have htrace : WordTrace (prefixWord ++ tailWord_2026805) baseStart_2026805 baseEnd_2026805 := by
    simpa [prefixWord, tailWord_2026805, baseEnd_2026805] using wordTrace_append hprefix tailTrace_2026805
  have hstable : (prefixWord ++ tailWord_2026805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026805).length < 2 ^ (prefixWord ++ tailWord_2026805).sum := by decide
  have hdescent : baseEnd_2026805 < baseStart_2026805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026820 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 6]
def baseStart_2026820 : Nat := 118140960795 + 2026820 * 2 ^ 59
def prefixEnd_2026820 : Nat := 4983230072969 + 3 ^ 40 * 2026820 * 2
def baseEnd_2026820 : Nat := 231273968921303398028629

theorem tailTrace_2026820 : CollatzResearch.WordTrace tailWord_2026820 prefixEnd_2026820 231273968921303398028629 := by
  unfold tailWord_2026820
  simp only [CollatzResearch.WordTrace]
  refine ⟨36962099258592384071218957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49282799011456512094958609 36962099258592384071218957)
  ·
    refine ⟨13860787221972144026707109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36962099258592384071218957 13860787221972144026707109)
    ·
      refine ⟨2598897604119777005007583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13860787221972144026707109 2598897604119777005007583)
      ·
        refine ⟨3898346406179665507511375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2598897604119777005007583 3898346406179665507511375)
        ·
          refine ⟨5847519609269498261267063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3898346406179665507511375 5847519609269498261267063)
          ·
            refine ⟨8771279413904247391900595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5847519609269498261267063 8771279413904247391900595)
            ·
              refine ⟨13156919120856371087850893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8771279413904247391900595 13156919120856371087850893)
              ·
                refine ⟨4933844670321139157944085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13156919120856371087850893 4933844670321139157944085)
                ·
                  refine ⟨231273968921303398028629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4933844670321139157944085 231273968921303398028629)
                  ·
                    rfl

theorem cell22_2026820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_2026820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026820 prefixEnd_2026820 := by exact prefixLift 2026820
  have htrace : WordTrace (prefixWord ++ tailWord_2026820) baseStart_2026820 baseEnd_2026820 := by
    simpa [prefixWord, tailWord_2026820, baseEnd_2026820] using wordTrace_append hprefix tailTrace_2026820
  have hstable : (prefixWord ++ tailWord_2026820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026820).length < 2 ^ (prefixWord ++ tailWord_2026820).sum := by decide
  have hdescent : baseEnd_2026820 < baseStart_2026820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026848 : List Nat := [2, 1, 1, 3, 4, 2, 1, 8]
def baseStart_2026848 : Nat := 118140960795 + 2026848 * 2 ^ 59
def prefixEnd_2026848 : Nat := 4983230072969 + 3 ^ 40 * 2026848 * 2
def baseEnd_2026848 : Nat := 77092387970680828265089

theorem tailTrace_2026848 : CollatzResearch.WordTrace tailWord_2026848 prefixEnd_2026848 77092387970680828265089 := by
  unfold tailWord_2026848
  simp only [CollatzResearch.WordTrace]
  refine ⟨36962609880541664462228599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49283479840722219282971465 36962609880541664462228599)
  ·
    refine ⟨55443914820812496693342899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36962609880541664462228599 55443914820812496693342899)
    ·
      refine ⟨83165872231218745040014349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55443914820812496693342899 83165872231218745040014349)
      ·
        refine ⟨31187202086707029390005381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83165872231218745040014349 31187202086707029390005381)
        ·
          refine ⟨5847600391257568010626009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31187202086707029390005381 5847600391257568010626009)
          ·
            refine ⟨4385700293443176007969507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5847600391257568010626009 4385700293443176007969507)
            ·
              refine ⟨6578550440164764011954261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385700293443176007969507 6578550440164764011954261)
              ·
                refine ⟨77092387970680828265089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6578550440164764011954261 77092387970680828265089)
                ·
                  rfl

theorem cell22_2026848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 8].length) (baseStart_2026848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026848 prefixEnd_2026848 := by exact prefixLift 2026848
  have htrace : WordTrace (prefixWord ++ tailWord_2026848) baseStart_2026848 baseEnd_2026848 := by
    simpa [prefixWord, tailWord_2026848, baseEnd_2026848] using wordTrace_append hprefix tailTrace_2026848
  have hstable : (prefixWord ++ tailWord_2026848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026848).length < 2 ^ (prefixWord ++ tailWord_2026848).sum := by decide
  have hdescent : baseEnd_2026848 < baseStart_2026848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026850 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2026850 : Nat := 118140960795 + 2026850 * 2 ^ 59
def prefixEnd_2026850 : Nat := 4983230072969 + 3 ^ 40 * 2026850 * 2
def baseEnd_2026850 : Nat := 693832176377000115835795

theorem tailTrace_2026850 : CollatzResearch.WordTrace tailWord_2026850 prefixEnd_2026850 693832176377000115835795 := by
  unfold tailWord_2026850
  simp only [CollatzResearch.WordTrace]
  refine ⟨18481323176769020816507501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49283528471384055510686669 18481323176769020816507501)
  ·
    refine ⟨6930496191288382806190313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18481323176769020816507501 6930496191288382806190313)
    ·
      refine ⟨5197872143466287104642735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6930496191288382806190313 5197872143466287104642735)
      ·
        refine ⟨7796808215199430656964103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5197872143466287104642735 7796808215199430656964103)
        ·
          refine ⟨11695212322799145985446155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7796808215199430656964103 11695212322799145985446155)
          ·
            refine ⟨17542818484198718978169233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11695212322799145985446155 17542818484198718978169233)
            ·
              refine ⟨13157113863149039233626925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17542818484198718978169233 13157113863149039233626925)
              ·
                refine ⟨4933917698680889712610097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13157113863149039233626925 4933917698680889712610097)
                ·
                  refine ⟨3700438274010667284457573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4933917698680889712610097 3700438274010667284457573)
                  ·
                    refine ⟨693832176377000115835795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3700438274010667284457573 693832176377000115835795)
                    ·
                      rfl

theorem cell22_2026850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2026850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026850 prefixEnd_2026850 := by exact prefixLift 2026850
  have htrace : WordTrace (prefixWord ++ tailWord_2026850) baseStart_2026850 baseEnd_2026850 := by
    simpa [prefixWord, tailWord_2026850, baseEnd_2026850] using wordTrace_append hprefix tailTrace_2026850
  have hstable : (prefixWord ++ tailWord_2026850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026850).length < 2 ^ (prefixWord ++ tailWord_2026850).sum := by decide
  have hdescent : baseEnd_2026850 < baseStart_2026850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026882 : List Nat := [3, 4, 2, 1, 1, 2, 2, 7]
def baseStart_2026882 : Nat := 118140960795 + 2026882 * 2 ^ 59
def prefixEnd_2026882 : Nat := 4983230072969 + 3 ^ 40 * 2026882 * 2
def baseEnd_2026882 : Nat := 77093681181218077670633

theorem tailTrace_2026882 : CollatzResearch.WordTrace tailWord_2026882 prefixEnd_2026882 77093681181218077670633 := by
  unfold tailWord_2026882
  simp only [CollatzResearch.WordTrace]
  refine ⟨18481614960740038182798725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49284306561973435154129933 18481614960740038182798725)
  ·
    refine ⟨3465302805138757159274761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18481614960740038182798725 3465302805138757159274761)
    ·
      refine ⟨2598977103854067869456071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3465302805138757159274761 2598977103854067869456071)
      ·
        refine ⟨3898465655781101804184107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2598977103854067869456071 3898465655781101804184107)
        ·
          refine ⟨5847698483671652706276161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3898465655781101804184107 5847698483671652706276161)
          ·
            refine ⟨4385773862753739529707121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5847698483671652706276161 4385773862753739529707121)
            ·
              refine ⟨3289330397065304647280341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4385773862753739529707121 3289330397065304647280341)
              ·
                refine ⟨77093681181218077670633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3289330397065304647280341 77093681181218077670633)
                ·
                  rfl

theorem cell22_2026882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_2026882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026882 prefixEnd_2026882 := by exact prefixLift 2026882
  have htrace : WordTrace (prefixWord ++ tailWord_2026882) baseStart_2026882 baseEnd_2026882 := by
    simpa [prefixWord, tailWord_2026882, baseEnd_2026882] using wordTrace_append hprefix tailTrace_2026882
  have hstable : (prefixWord ++ tailWord_2026882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026882).length < 2 ^ (prefixWord ++ tailWord_2026882).sum := by decide
  have hdescent : baseEnd_2026882 < baseStart_2026882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026970 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_2026970 : Nat := 118140960795 + 2026970 * 2 ^ 59
def prefixEnd_2026970 : Nat := 4983230072969 + 3 ^ 40 * 2026970 * 2
def baseEnd_2026970 : Nat := 693873254829359802835427

theorem tailTrace_2026970 : CollatzResearch.WordTrace tailWord_2026970 prefixEnd_2026970 693873254829359802835427 := by
  unfold tailWord_2026970
  simp only [CollatzResearch.WordTrace]
  refine ⟨18482417366660335940099591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49286446311094229173598909 18482417366660335940099591)
  ·
    refine ⟨27723626049990503910149387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18482417366660335940099591 27723626049990503910149387)
    ·
      refine ⟨41585439074985755865224081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27723626049990503910149387 41585439074985755865224081)
      ·
        refine ⟨31189079306239316898918061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41585439074985755865224081 31189079306239316898918061)
        ·
          refine ⟨11695904739839743837094273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31189079306239316898918061 11695904739839743837094273)
          ·
            refine ⟨8771928554879807877820705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11695904739839743837094273 8771928554879807877820705)
            ·
              refine ⟨6578946416159855908365529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8771928554879807877820705 6578946416159855908365529)
              ·
                refine ⟨4934209812119891931274147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6578946416159855908365529 4934209812119891931274147)
                ·
                  refine ⟨7401314718179837896911221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4934209812119891931274147 7401314718179837896911221)
                  ·
                    refine ⟨693873254829359802835427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7401314718179837896911221 693873254829359802835427)
                    ·
                      rfl

theorem cell22_2026970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_2026970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2026970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2026970 prefixEnd_2026970 := by exact prefixLift 2026970
  have htrace : WordTrace (prefixWord ++ tailWord_2026970) baseStart_2026970 baseEnd_2026970 := by
    simpa [prefixWord, tailWord_2026970, baseEnd_2026970] using wordTrace_append hprefix tailTrace_2026970
  have hstable : (prefixWord ++ tailWord_2026970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026970).length < 2 ^ (prefixWord ++ tailWord_2026970).sum := by decide
  have hdescent : baseEnd_2026970 < baseStart_2026970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027045 : List Nat := [1, 3, 1, 2, 2, 1, 1, 6, 5]
def baseStart_2027045 : Nat := 118140960795 + 2027045 * 2 ^ 59
def prefixEnd_2027045 : Nat := 4983230072969 + 3 ^ 40 * 2027045 * 2
def baseEnd_2027045 : Nat := 231299642954028202403399

theorem tailTrace_2027045 : CollatzResearch.WordTrace tailWord_2027045 prefixEnd_2027045 231299642954028202403399 := by
  unfold tailWord_2027045
  simp only [CollatzResearch.WordTrace]
  refine ⟨73932404941369631569378589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49288269960913087712919059 73932404941369631569378589)
  ·
    refine ⟨27724651853013611838516971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73932404941369631569378589 27724651853013611838516971)
    ·
      refine ⟨41586977779520417757775457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27724651853013611838516971 41586977779520417757775457)
      ·
        refine ⟨31190233334640313318331593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41586977779520417757775457 31190233334640313318331593)
        ·
          refine ⟨23392675000980234988748695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31190233334640313318331593 23392675000980234988748695)
          ·
            refine ⟨35089012501470352483123043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23392675000980234988748695 35089012501470352483123043)
            ·
              refine ⟨52633518752205528724684565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35089012501470352483123043 52633518752205528724684565)
              ·
                refine ⟨2467196191509634158969589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52633518752205528724684565 2467196191509634158969589)
                ·
                  refine ⟨231299642954028202403399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2467196191509634158969589 231299642954028202403399)
                  ·
                    rfl

theorem cell22_2027045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_2027045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027045 prefixEnd_2027045 := by exact prefixLift 2027045
  have htrace : WordTrace (prefixWord ++ tailWord_2027045) baseStart_2027045 baseEnd_2027045 := by
    simpa [prefixWord, tailWord_2027045, baseEnd_2027045] using wordTrace_append hprefix tailTrace_2027045
  have hstable : (prefixWord ++ tailWord_2027045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027045).length < 2 ^ (prefixWord ++ tailWord_2027045).sum := by decide
  have hdescent : baseEnd_2027045 < baseStart_2027045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027105 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 3, 5]
def baseStart_2027105 : Nat := 118140960795 + 2027105 * 2 ^ 59
def prefixEnd_2027105 : Nat := 4983230072969 + 3 ^ 40 * 2027105 * 2
def baseEnd_2027105 : Nat := 693919468088264450710013

theorem tailTrace_2027105 : CollatzResearch.WordTrace tailWord_2027105 prefixEnd_2027105 693919468088264450710013 := by
  unfold tailWord_2027105
  simp only [CollatzResearch.WordTrace]
  refine ⟨73934593321152261816562769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49289728880768174544375179 73934593321152261816562769)
  ·
    refine ⟨55450944990864196362422077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73934593321152261816562769 55450944990864196362422077)
    ·
      refine ⟨20794104371574073635908279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55450944990864196362422077 20794104371574073635908279)
      ·
        refine ⟨31191156557361110453862419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20794104371574073635908279 31191156557361110453862419)
        ·
          refine ⟨46786734836041665680793629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31191156557361110453862419 46786734836041665680793629)
          ·
            refine ⟨17545025563515624630297611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46786734836041665680793629 17545025563515624630297611)
            ·
              refine ⟨26317538345273436945446417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17545025563515624630297611 26317538345273436945446417)
              ·
                refine ⟨19738153758955077709084813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26317538345273436945446417 19738153758955077709084813)
                ·
                  refine ⟨7401807659608154140906805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19738153758955077709084813 7401807659608154140906805)
                  ·
                    refine ⟨693919468088264450710013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7401807659608154140906805 693919468088264450710013)
                    ·
                      rfl

theorem cell22_2027105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_2027105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027105 prefixEnd_2027105 := by exact prefixLift 2027105
  have htrace : WordTrace (prefixWord ++ tailWord_2027105) baseStart_2027105 baseEnd_2027105 := by
    simpa [prefixWord, tailWord_2027105, baseEnd_2027105] using wordTrace_append hprefix tailTrace_2027105
  have hstable : (prefixWord ++ tailWord_2027105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027105).length < 2 ^ (prefixWord ++ tailWord_2027105).sum := by decide
  have hdescent : baseEnd_2027105 < baseStart_2027105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027122 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_2027122 : Nat := 118140960795 + 2027122 * 2 ^ 59
def prefixEnd_2027122 : Nat := 4983230072969 + 3 ^ 40 * 2027122 * 2
def baseEnd_2027122 : Nat := 693925287535682073034961

theorem tailTrace_2027122 : CollatzResearch.WordTrace tailWord_2027122 prefixEnd_2027122 693925287535682073034961 := by
  unfold tailWord_2027122
  simp only [CollatzResearch.WordTrace]
  refine ⟨18483803340522668429982905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49290142241393782479954413 18483803340522668429982905)
  ·
    refine ⟨13862852505392001322487179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18483803340522668429982905 13862852505392001322487179)
    ·
      refine ⟨20794278758088001983730769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13862852505392001322487179 20794278758088001983730769)
      ·
        refine ⟨15595709068566001487798077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20794278758088001983730769 15595709068566001487798077)
        ·
          refine ⟨5848390900712250557924279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15595709068566001487798077 5848390900712250557924279)
          ·
            refine ⟨8772586351068375836886419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5848390900712250557924279 8772586351068375836886419)
            ·
              refine ⟨13158879526602563755329629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8772586351068375836886419 13158879526602563755329629)
              ·
                refine ⟨4934579822475961408248611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13158879526602563755329629 4934579822475961408248611)
                ·
                  refine ⟨7401869733713942112372917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4934579822475961408248611 7401869733713942112372917)
                  ·
                    refine ⟨693925287535682073034961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7401869733713942112372917 693925287535682073034961)
                    ·
                      rfl

theorem cell22_2027122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_2027122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027122 prefixEnd_2027122 := by exact prefixLift 2027122
  have htrace : WordTrace (prefixWord ++ tailWord_2027122) baseStart_2027122 baseEnd_2027122 := by
    simpa [prefixWord, tailWord_2027122, baseEnd_2027122] using wordTrace_append hprefix tailTrace_2027122
  have hstable : (prefixWord ++ tailWord_2027122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027122).length < 2 ^ (prefixWord ++ tailWord_2027122).sum := by decide
  have hdescent : baseEnd_2027122 < baseStart_2027122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027137 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 1, 6]
def baseStart_2027137 : Nat := 118140960795 + 2027137 * 2 ^ 59
def prefixEnd_2027137 : Nat := 4983230072969 + 3 ^ 40 * 2027137 * 2
def baseEnd_2027137 : Nat := 693930422342227033909915

theorem tailTrace_2027137 : CollatzResearch.WordTrace tailWord_2027137 prefixEnd_2027137 693930422342227033909915 := by
  unfold tailWord_2027137
  simp only [CollatzResearch.WordTrace]
  refine ⟨73935760457036331281727665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49290506971357554187818443 73935760457036331281727665)
  ·
    refine ⟨55451820342777248461295749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73935760457036331281727665 55451820342777248461295749)
    ·
      refine ⟨10397216314270734086492953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55451820342777248461295749 10397216314270734086492953)
      ·
        refine ⟨7797912235703050564869715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10397216314270734086492953 7797912235703050564869715)
        ·
          refine ⟨11696868353554575847304573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797912235703050564869715 11696868353554575847304573)
          ·
            refine ⟨4386325632582965942739215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11696868353554575847304573 4386325632582965942739215)
            ·
              refine ⟨6579488448874448914108823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4386325632582965942739215 6579488448874448914108823)
              ·
                refine ⟨9869232673311673371163235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579488448874448914108823 9869232673311673371163235)
                ·
                  refine ⟨14803849009967510056744853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9869232673311673371163235 14803849009967510056744853)
                  ·
                    refine ⟨693930422342227033909915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14803849009967510056744853 693930422342227033909915)
                    ·
                      rfl

theorem cell22_2027137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_2027137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027137 prefixEnd_2027137 := by exact prefixLift 2027137
  have htrace : WordTrace (prefixWord ++ tailWord_2027137) baseStart_2027137 baseEnd_2027137 := by
    simpa [prefixWord, tailWord_2027137, baseEnd_2027137] using wordTrace_append hprefix tailTrace_2027137
  have hstable : (prefixWord ++ tailWord_2027137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027137).length < 2 ^ (prefixWord ++ tailWord_2027137).sum := by decide
  have hdescent : baseEnd_2027137 < baseStart_2027137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027156 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2027156 : Nat := 118140960795 + 2027156 * 2 ^ 59
def prefixEnd_2027156 : Nat := 4983230072969 + 3 ^ 40 * 2027156 * 2
def baseEnd_2027156 : Nat := 693936926430517317684857

theorem tailTrace_2027156 : CollatzResearch.WordTrace tailWord_2027156 prefixEnd_2027156 693936926430517317684857 := by
  unfold tailWord_2027156
  simp only [CollatzResearch.WordTrace]
  refine ⟨36968226721983748763334661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49290968962644998351112881 36968226721983748763334661)
  ·
    refine ⟨6931542510371952893125249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36968226721983748763334661 6931542510371952893125249)
    ·
      refine ⟨5198656882778964669843937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6931542510371952893125249 5198656882778964669843937)
      ·
        refine ⟨3898992662084223502382953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5198656882778964669843937 3898992662084223502382953)
        ·
          refine ⟨2924244496563167626787215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3898992662084223502382953 2924244496563167626787215)
          ·
            refine ⟨4386366744844751440180823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2924244496563167626787215 4386366744844751440180823)
            ·
              refine ⟨6579550117267127160271235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4386366744844751440180823 6579550117267127160271235)
              ·
                refine ⟨9869325175900690740406853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579550117267127160271235 9869325175900690740406853)
                ·
                  refine ⟨1850498470481379513826285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9869325175900690740406853 1850498470481379513826285)
                  ·
                    refine ⟨693936926430517317684857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1850498470481379513826285 693936926430517317684857)
                    ·
                      rfl

theorem cell22_2027156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2027156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027156 prefixEnd_2027156 := by exact prefixLift 2027156
  have htrace : WordTrace (prefixWord ++ tailWord_2027156) baseStart_2027156 baseEnd_2027156 := by
    simpa [prefixWord, tailWord_2027156, baseEnd_2027156] using wordTrace_append hprefix tailTrace_2027156
  have hstable : (prefixWord ++ tailWord_2027156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027156).length < 2 ^ (prefixWord ++ tailWord_2027156).sum := by decide
  have hdescent : baseEnd_2027156 < baseStart_2027156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027195 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 1, 7]
def baseStart_2027195 : Nat := 118140960795 + 2027195 * 2 ^ 59
def prefixEnd_2027195 : Nat := 4983230072969 + 3 ^ 40 * 2027195 * 2
def baseEnd_2027195 : Nat := 693950276927534215959737

theorem tailTrace_2027195 : CollatzResearch.WordTrace tailWord_2027195 prefixEnd_2027195 693950276927534215959737 := by
  unfold tailWord_2027195
  simp only [CollatzResearch.WordTrace]
  refine ⟨73937875890826207187339039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49291917260550804791559359 73937875890826207187339039)
  ·
    refine ⟨110906813836239310781008559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73937875890826207187339039 110906813836239310781008559)
    ·
      refine ⟨166360220754358966171512839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110906813836239310781008559 166360220754358966171512839)
      ·
        refine ⟨249540331131538449257269259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166360220754358966171512839 249540331131538449257269259)
        ·
          refine ⟨374310496697307673885903889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249540331131538449257269259 374310496697307673885903889)
          ·
            refine ⟨280732872522980755414427917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374310496697307673885903889 280732872522980755414427917)
            ·
              refine ⟨105274827196117783280410469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280732872522980755414427917 105274827196117783280410469)
              ·
                refine ⟨19739030099272084365076963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105274827196117783280410469 19739030099272084365076963)
                ·
                  refine ⟨29608545148908126547615445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19739030099272084365076963 29608545148908126547615445)
                  ·
                    refine ⟨693950276927534215959737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29608545148908126547615445 693950276927534215959737)
                    ·
                      rfl

theorem cell22_2027195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 7].length) (baseStart_2027195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027195 prefixEnd_2027195 := by exact prefixLift 2027195
  have htrace : WordTrace (prefixWord ++ tailWord_2027195) baseStart_2027195 baseEnd_2027195 := by
    simpa [prefixWord, tailWord_2027195, baseEnd_2027195] using wordTrace_append hprefix tailTrace_2027195
  have hstable : (prefixWord ++ tailWord_2027195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027195).length < 2 ^ (prefixWord ++ tailWord_2027195).sum := by decide
  have hdescent : baseEnd_2027195 < baseStart_2027195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027242 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 6]
def baseStart_2027242 : Nat := 118140960795 + 2027242 * 2 ^ 59
def prefixEnd_2027242 : Nat := 4983230072969 + 3 ^ 40 * 2027242 * 2
def baseEnd_2027242 : Nat := 231322121996013920011531

theorem tailTrace_2027242 : CollatzResearch.WordTrace tailWord_2027242 prefixEnd_2027242 231322121996013920011531 := by
  unfold tailWord_2027242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18484897530413983553574995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49293060081103956142866653 18484897530413983553574995)
  ·
    refine ⟨27727346295620975330362493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18484897530413983553574995 27727346295620975330362493)
    ·
      refine ⟨10397754860857865748885935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27727346295620975330362493 10397754860857865748885935)
      ·
        refine ⟨15596632291286798623328903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10397754860857865748885935 15596632291286798623328903)
        ·
          refine ⟨23394948436930197934993355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15596632291286798623328903 23394948436930197934993355)
          ·
            refine ⟨35092422655395296902490033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23394948436930197934993355 35092422655395296902490033)
            ·
              refine ⟨26319316991546472676867525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35092422655395296902490033 26319316991546472676867525)
              ·
                refine ⟨4934871935914963626912661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26319316991546472676867525 4934871935914963626912661)
                ·
                  refine ⟨231322121996013920011531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4934871935914963626912661 231322121996013920011531)
                  ·
                    rfl

theorem cell22_2027242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_2027242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027242 prefixEnd_2027242 := by exact prefixLift 2027242
  have htrace : WordTrace (prefixWord ++ tailWord_2027242) baseStart_2027242 baseEnd_2027242 := by
    simpa [prefixWord, tailWord_2027242, baseEnd_2027242] using wordTrace_append hprefix tailTrace_2027242
  have hstable : (prefixWord ++ tailWord_2027242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027242).length < 2 ^ (prefixWord ++ tailWord_2027242).sum := by decide
  have hdescent : baseEnd_2027242 < baseStart_2027242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027244 : List Nat := [2, 2, 1, 1, 2, 2, 5, 2, 1, 4]
def baseStart_2027244 : Nat := 118140960795 + 2027244 * 2 ^ 59
def prefixEnd_2027244 : Nat := 4983230072969 + 3 ^ 40 * 2027244 * 2
def baseEnd_2027244 : Nat := 693967050628914421484587

theorem tailTrace_2027244 : CollatzResearch.WordTrace tailWord_2027244 prefixEnd_2027244 693967050628914421484587 := by
  unfold tailWord_2027244
  simp only [CollatzResearch.WordTrace]
  refine ⟨36969831533824344277936393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49293108711765792370581857 36969831533824344277936393)
  ·
    refine ⟨27727373650368258208452295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36969831533824344277936393 27727373650368258208452295)
    ·
      refine ⟨41591060475552387312678443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27727373650368258208452295 41591060475552387312678443)
      ·
        refine ⟨62386590713328580969017665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41591060475552387312678443 62386590713328580969017665)
        ·
          refine ⟨46789943034996435726763249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62386590713328580969017665 46789943034996435726763249)
          ·
            refine ⟨35092457276247326795072437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46789943034996435726763249 35092457276247326795072437)
            ·
              refine ⟨3289917869648186887038041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35092457276247326795072437 3289917869648186887038041)
              ·
                refine ⟨2467438402236140165278531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3289917869648186887038041 2467438402236140165278531)
                ·
                  refine ⟨3701157603354210247917797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467438402236140165278531 3701157603354210247917797)
                  ·
                    refine ⟨693967050628914421484587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3701157603354210247917797 693967050628914421484587)
                    ·
                      rfl

theorem cell22_2027244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_2027244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027244 prefixEnd_2027244 := by exact prefixLift 2027244
  have htrace : WordTrace (prefixWord ++ tailWord_2027244) baseStart_2027244 baseEnd_2027244 := by
    simpa [prefixWord, tailWord_2027244, baseEnd_2027244] using wordTrace_append hprefix tailTrace_2027244
  have hstable : (prefixWord ++ tailWord_2027244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027244).length < 2 ^ (prefixWord ++ tailWord_2027244).sum := by decide
  have hdescent : baseEnd_2027244 < baseStart_2027244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027276 : List Nat := [2, 2, 1, 2, 2, 1, 6, 2, 4]
def baseStart_2027276 : Nat := 118140960795 + 2027276 * 2 ^ 59
def prefixEnd_2027276 : Nat := 4983230072969 + 3 ^ 40 * 2027276 * 2
def baseEnd_2027276 : Nat := 231326001627625668228163

theorem tailTrace_2027276 : CollatzResearch.WordTrace tailWord_2027276 prefixEnd_2027276 231326001627625668228163 := by
  unfold tailWord_2027276
  simp only [CollatzResearch.WordTrace]
  refine ⟨36970415101766379010518841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49293886802355172014025121 36970415101766379010518841)
  ·
    refine ⟨27727811326324784257889131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36970415101766379010518841 27727811326324784257889131)
    ·
      refine ⟨41591716989487176386833697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27727811326324784257889131 41591716989487176386833697)
      ·
        refine ⟨31193787742115382290125273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41591716989487176386833697 31193787742115382290125273)
        ·
          refine ⟨23395340806586536717593955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31193787742115382290125273 23395340806586536717593955)
          ·
            refine ⟨35093011209879805076390933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23395340806586536717593955 35093011209879805076390933)
            ·
              refine ⟨1644984900463115862955825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35093011209879805076390933 1644984900463115862955825)
              ·
                refine ⟨1233738675347336897216869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644984900463115862955825 1233738675347336897216869)
                ·
                  refine ⟨231326001627625668228163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1233738675347336897216869 231326001627625668228163)
                  ·
                    rfl

theorem cell22_2027276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_2027276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027276 prefixEnd_2027276 := by exact prefixLift 2027276
  have htrace : WordTrace (prefixWord ++ tailWord_2027276) baseStart_2027276 baseEnd_2027276 := by
    simpa [prefixWord, tailWord_2027276, baseEnd_2027276] using wordTrace_append hprefix tailTrace_2027276
  have hstable : (prefixWord ++ tailWord_2027276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027276).length < 2 ^ (prefixWord ++ tailWord_2027276).sum := by decide
  have hdescent : baseEnd_2027276 < baseStart_2027276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027336 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 3, 3]
def baseStart_2027336 : Nat := 118140960795 + 2027336 * 2 ^ 59
def prefixEnd_2027336 : Nat := 4983230072969 + 3 ^ 40 * 2027336 * 2
def baseEnd_2027336 : Nat := 693998544109056848184305

theorem tailTrace_2027336 : CollatzResearch.WordTrace tailWord_2027336 prefixEnd_2027336 693998544109056848184305 := by
  unfold tailWord_2027336
  simp only [CollatzResearch.WordTrace]
  refine ⟨36971509291657694134110931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49295345722210258845481241 36971509291657694134110931)
  ·
    refine ⟨55457263937486541201166397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36971509291657694134110931 55457263937486541201166397)
    ·
      refine ⟨20796473976557452950437399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55457263937486541201166397 20796473976557452950437399)
      ·
        refine ⟨31194710964836179425656099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20796473976557452950437399 31194710964836179425656099)
        ·
          refine ⟨46792066447254269138484149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31194710964836179425656099 46792066447254269138484149)
          ·
            refine ⟨4386756229430087731732889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46792066447254269138484149 4386756229430087731732889)
            ·
              refine ⟨3290067172072565798799667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4386756229430087731732889 3290067172072565798799667)
              ·
                refine ⟨4935100758108848698199501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290067172072565798799667 4935100758108848698199501)
                ·
                  refine ⟨1850662784290818261824813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4935100758108848698199501 1850662784290818261824813)
                  ·
                    refine ⟨693998544109056848184305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1850662784290818261824813 693998544109056848184305)
                    ·
                      rfl

theorem cell22_2027336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_2027336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027336 prefixEnd_2027336 := by exact prefixLift 2027336
  have htrace : WordTrace (prefixWord ++ tailWord_2027336) baseStart_2027336 baseEnd_2027336 := by
    simpa [prefixWord, tailWord_2027336, baseEnd_2027336] using wordTrace_append hprefix tailTrace_2027336
  have hstable : (prefixWord ++ tailWord_2027336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027336).length < 2 ^ (prefixWord ++ tailWord_2027336).sum := by decide
  have hdescent : baseEnd_2027336 < baseStart_2027336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027400 : List Nat := [2, 1, 3, 3, 4, 1, 2, 1, 5]
def baseStart_2027400 : Nat := 118140960795 + 2027400 * 2 ^ 59
def prefixEnd_2027400 : Nat := 4983230072969 + 3 ^ 40 * 2027400 * 2
def baseEnd_2027400 : Nat := 231340150872327338194703

theorem tailTrace_2027400 : CollatzResearch.WordTrace tailWord_2027400 prefixEnd_2027400 231340150872327338194703 := by
  unfold tailWord_2027400
  simp only [CollatzResearch.WordTrace]
  refine ⟨36972676427541763599275827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49296901903389018132367769 36972676427541763599275827)
  ·
    refine ⟨55459014641312645398913741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36972676427541763599275827 55459014641312645398913741)
    ·
      refine ⟨20797130490492242024592653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55459014641312645398913741 20797130490492242024592653)
      ·
        refine ⟨7798923933934590759222245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20797130490492242024592653 7798923933934590759222245)
        ·
          refine ⟨1462298237612735767354171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7798923933934590759222245 1462298237612735767354171)
          ·
            refine ⟨2193447356419103651031257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462298237612735767354171 2193447356419103651031257)
            ·
              refine ⟨1645085517314327738273443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2193447356419103651031257 1645085517314327738273443)
              ·
                refine ⟨2467628275971491607410165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645085517314327738273443 2467628275971491607410165)
                ·
                  refine ⟨231340150872327338194703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2467628275971491607410165 231340150872327338194703)
                  ·
                    rfl

theorem cell22_2027400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 5].length) (baseStart_2027400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027400 prefixEnd_2027400 := by exact prefixLift 2027400
  have htrace : WordTrace (prefixWord ++ tailWord_2027400) baseStart_2027400 baseEnd_2027400 := by
    simpa [prefixWord, tailWord_2027400, baseEnd_2027400] using wordTrace_append hprefix tailTrace_2027400
  have hstable : (prefixWord ++ tailWord_2027400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027400).length < 2 ^ (prefixWord ++ tailWord_2027400).sum := by decide
  have hdescent : baseEnd_2027400 < baseStart_2027400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027438 : List Nat := [4, 1, 5, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2027438 : Nat := 118140960795 + 2027438 * 2 ^ 59
def prefixEnd_2027438 : Nat := 4983230072969 + 3 ^ 40 * 2027438 * 2
def baseEnd_2027438 : Nat := 694033460793562582133993

theorem tailTrace_2027438 : CollatzResearch.WordTrace tailWord_2027438 prefixEnd_2027438 694033460793562582133993 := by
  unfold tailWord_2027438
  simp only [CollatzResearch.WordTrace]
  refine ⟨9243342353618232461054371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49297825885963906458956645 9243342353618232461054371)
  ·
    refine ⟨13865013530427348691581557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9243342353618232461054371 13865013530427348691581557)
    ·
      refine ⟨1299845018477563939835771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13865013530427348691581557 1299845018477563939835771)
      ·
        refine ⟨1949767527716345909753657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299845018477563939835771 1949767527716345909753657)
        ·
          refine ⟨1462325645787259432315243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1949767527716345909753657 1462325645787259432315243)
          ·
            refine ⟨2193488468680889148472865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462325645787259432315243 2193488468680889148472865)
            ·
              refine ⟨1645116351510666861354649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2193488468680889148472865 1645116351510666861354649)
              ·
                refine ⟨1233837263633000146015987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1645116351510666861354649 1233837263633000146015987)
                ·
                  refine ⟨1850755895449500219023981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1233837263633000146015987 1850755895449500219023981)
                  ·
                    refine ⟨694033460793562582133993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1850755895449500219023981 694033460793562582133993)
                    ·
                      rfl

theorem cell22_2027438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2027438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027438 prefixEnd_2027438 := by exact prefixLift 2027438
  have htrace : WordTrace (prefixWord ++ tailWord_2027438) baseStart_2027438 baseEnd_2027438 := by
    simpa [prefixWord, tailWord_2027438, baseEnd_2027438] using wordTrace_append hprefix tailTrace_2027438
  have hstable : (prefixWord ++ tailWord_2027438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027438).length < 2 ^ (prefixWord ++ tailWord_2027438).sum := by decide
  have hdescent : baseEnd_2027438 < baseStart_2027438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027441 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 2, 4]
def baseStart_2027441 : Nat := 118140960795 + 2027441 * 2 ^ 59
def prefixEnd_2027441 : Nat := 4983230072969 + 3 ^ 40 * 2027441 * 2
def baseEnd_2027441 : Nat := 694034487754871574308983

theorem tailTrace_2027441 : CollatzResearch.WordTrace tailWord_2027441 prefixEnd_2027441 694034487754871574308983 := by
  unfold tailWord_2027441
  simp only [CollatzResearch.WordTrace]
  refine ⟨73946848247934991200794177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49297898831956660800529451 73946848247934991200794177)
  ·
    refine ⟨55460136185951243400595633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73946848247934991200794177 55460136185951243400595633)
    ·
      refine ⟨41595102139463432550446725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55460136185951243400595633 41595102139463432550446725)
      ·
        refine ⟨7799081651149393603208761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41595102139463432550446725 7799081651149393603208761)
        ·
          refine ⟨5849311238362045202406571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7799081651149393603208761 5849311238362045202406571)
          ·
            refine ⟨8773966857543067803609857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5849311238362045202406571 8773966857543067803609857)
            ·
              refine ⟨6580475143157300852707393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8773966857543067803609857 6580475143157300852707393)
              ·
                refine ⟨4935356357367975639530545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6580475143157300852707393 4935356357367975639530545)
                ·
                  refine ⟨3701517268025981729647909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4935356357367975639530545 3701517268025981729647909)
                  ·
                    refine ⟨694034487754871574308983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3701517268025981729647909 694034487754871574308983)
                    ·
                      rfl

theorem cell22_2027441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_2027441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027441 prefixEnd_2027441 := by exact prefixLift 2027441
  have htrace : WordTrace (prefixWord ++ tailWord_2027441) baseStart_2027441 baseEnd_2027441 := by
    simpa [prefixWord, tailWord_2027441, baseEnd_2027441] using wordTrace_append hprefix tailTrace_2027441
  have hstable : (prefixWord ++ tailWord_2027441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027441).length < 2 ^ (prefixWord ++ tailWord_2027441).sum := by decide
  have hdescent : baseEnd_2027441 < baseStart_2027441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027445 : List Nat := [1, 3, 3, 2, 1, 4, 2, 2, 4]
def baseStart_2027445 : Nat := 118140960795 + 2027445 * 2 ^ 59
def prefixEnd_2027445 : Nat := 4983230072969 + 3 ^ 40 * 2027445 * 2
def baseEnd_2027445 : Nat := 231345285678872299069657

theorem tailTrace_2027445 : CollatzResearch.WordTrace tailWord_2027445 prefixEnd_2027445 231345285678872299069657 := by
  unfold tailWord_2027445
  simp only [CollatzResearch.WordTrace]
  refine ⟨73946994139920499883939789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49297996093280333255959859 73946994139920499883939789)
  ·
    refine ⟨27730122802470187456477421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73946994139920499883939789 27730122802470187456477421)
    ·
      refine ⟨10398796050926320296179033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27730122802470187456477421 10398796050926320296179033)
      ·
        refine ⟨7799097038194740222134275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10398796050926320296179033 7799097038194740222134275)
        ·
          refine ⟨11698645557292110333201413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7799097038194740222134275 11698645557292110333201413)
          ·
            refine ⟨2193496041992270687475265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11698645557292110333201413 2193496041992270687475265)
            ·
              refine ⟨1645122031494203015606449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2193496041992270687475265 1645122031494203015606449)
              ·
                refine ⟨1233841523620652261704837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1645122031494203015606449 1233841523620652261704837)
                ·
                  refine ⟨231345285678872299069657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1233841523620652261704837 231345285678872299069657)
                  ·
                    rfl

theorem cell22_2027445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_2027445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027445 prefixEnd_2027445 := by exact prefixLift 2027445
  have htrace : WordTrace (prefixWord ++ tailWord_2027445) baseStart_2027445 baseEnd_2027445 := by
    simpa [prefixWord, tailWord_2027445, baseEnd_2027445] using wordTrace_append hprefix tailTrace_2027445
  have hstable : (prefixWord ++ tailWord_2027445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027445).length < 2 ^ (prefixWord ++ tailWord_2027445).sum := by decide
  have hdescent : baseEnd_2027445 < baseStart_2027445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027471 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 3, 3]
def baseStart_2027471 : Nat := 118140960795 + 2027471 * 2 ^ 59
def prefixEnd_2027471 : Nat := 4983230072969 + 3 ^ 40 * 2027471 * 2
def baseEnd_2027471 : Nat := 694044757367961496058891

theorem tailTrace_2027471 : CollatzResearch.WordTrace tailWord_2027471 prefixEnd_2027471 694044757367961496058891 := by
  unfold tailWord_2027471
  simp only [CollatzResearch.WordTrace]
  refine ⟨73947942437826306324386267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49298628291884204216257511 73947942437826306324386267)
  ·
    refine ⟨110921913656739459486579401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73947942437826306324386267 110921913656739459486579401)
    ·
      refine ⟨83191435242554594614934551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110921913656739459486579401 83191435242554594614934551)
      ·
        refine ⟨124787152863831891922401827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83191435242554594614934551 124787152863831891922401827)
        ·
          refine ⟨187180729295747837883602741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124787152863831891922401827 187180729295747837883602741)
          ·
            refine ⟨17548193371476359801587757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187180729295747837883602741 17548193371476359801587757)
            ·
              refine ⟨6580572514303634925595409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17548193371476359801587757 6580572514303634925595409)
              ·
                refine ⟨4935429385727726194196557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6580572514303634925595409 4935429385727726194196557)
                ·
                  refine ⟨1850786019647897322823709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4935429385727726194196557 1850786019647897322823709)
                  ·
                    refine ⟨694044757367961496058891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1850786019647897322823709 694044757367961496058891)
                    ·
                      rfl

theorem cell22_2027471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 3].length) (baseStart_2027471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027471 prefixEnd_2027471 := by exact prefixLift 2027471
  have htrace : WordTrace (prefixWord ++ tailWord_2027471) baseStart_2027471 baseEnd_2027471 := by
    simpa [prefixWord, tailWord_2027471, baseEnd_2027471] using wordTrace_append hprefix tailTrace_2027471
  have hstable : (prefixWord ++ tailWord_2027471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027471).length < 2 ^ (prefixWord ++ tailWord_2027471).sum := by decide
  have hdescent : baseEnd_2027471 < baseStart_2027471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027548 : List Nat := [2, 2, 3, 1, 3, 1, 2, 3, 1, 4]
def baseStart_2027548 : Nat := 118140960795 + 2027548 * 2 ^ 59
def prefixEnd_2027548 : Nat := 4983230072969 + 3 ^ 40 * 2027548 * 2
def baseEnd_2027548 : Nat := 694071116041558961883655

theorem tailTrace_2027548 : CollatzResearch.WordTrace tailWord_2027548 prefixEnd_2027548 694071116041558961883655 := by
  unfold tailWord_2027548
  simp only [CollatzResearch.WordTrace]
  refine ⟨36975375429273674237469649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49300500572364898983292865 36975375429273674237469649)
  ·
    refine ⟨27731531571955255678102237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36975375429273674237469649 27731531571955255678102237)
    ·
      refine ⟨10399324339483220879288339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27731531571955255678102237 10399324339483220879288339)
      ·
        refine ⟨15598986509224831318932509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10399324339483220879288339 15598986509224831318932509)
        ·
          refine ⟨5849619940959311744599691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15598986509224831318932509 5849619940959311744599691)
          ·
            refine ⟨8774429911438967616899537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5849619940959311744599691 8774429911438967616899537)
            ·
              refine ⟨6580822433579225712674653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8774429911438967616899537 6580822433579225712674653)
              ·
                refine ⟨2467808412592209642252995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6580822433579225712674653 2467808412592209642252995)
                ·
                  refine ⟨3701712618888314463379493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467808412592209642252995 3701712618888314463379493)
                  ·
                    refine ⟨694071116041558961883655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3701712618888314463379493 694071116041558961883655)
                    ·
                      rfl

theorem cell22_2027548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_2027548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027548 prefixEnd_2027548 := by exact prefixLift 2027548
  have htrace : WordTrace (prefixWord ++ tailWord_2027548) baseStart_2027548 baseEnd_2027548 := by
    simpa [prefixWord, tailWord_2027548, baseEnd_2027548] using wordTrace_append hprefix tailTrace_2027548
  have hstable : (prefixWord ++ tailWord_2027548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027548).length < 2 ^ (prefixWord ++ tailWord_2027548).sum := by decide
  have hdescent : baseEnd_2027548 < baseStart_2027548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027582 : List Nat := [4, 2, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_2027582 : Nat := 118140960795 + 2027582 * 2 ^ 59
def prefixEnd_2027582 : Nat := 4983230072969 + 3 ^ 40 * 2027582 * 2
def baseEnd_2027582 : Nat := 694082754936394206533551

theorem tailTrace_2027582 : CollatzResearch.WordTrace tailWord_2027582 prefixEnd_2027582 694082754936394206533551 := by
  unfold tailWord_2027582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9243998867553021535209625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49301327293616114854451333 9243998867553021535209625)
  ·
    refine ⟨6932999150664766151407219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9243998867553021535209625 6932999150664766151407219)
    ·
      refine ⟨10399498725997149227110829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6932999150664766151407219 10399498725997149227110829)
      ·
        refine ⟨3899812022248930960166561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10399498725997149227110829 3899812022248930960166561)
        ·
          refine ⟨2924859016686698220124921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3899812022248930960166561 2924859016686698220124921)
          ·
            refine ⟨2193644262515023665093691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2924859016686698220124921 2193644262515023665093691)
            ·
              refine ⟨3290466393772535497640537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193644262515023665093691 3290466393772535497640537)
              ·
                refine ⟨2467849795329401623230403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3290466393772535497640537 2467849795329401623230403)
                ·
                  refine ⟨3701774692994102434845605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467849795329401623230403 3701774692994102434845605)
                  ·
                    refine ⟨694082754936394206533551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3701774692994102434845605 694082754936394206533551)
                    ·
                      rfl

theorem cell22_2027582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_2027582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027582 prefixEnd_2027582 := by exact prefixLift 2027582
  have htrace : WordTrace (prefixWord ++ tailWord_2027582) baseStart_2027582 baseEnd_2027582 := by
    simpa [prefixWord, tailWord_2027582, baseEnd_2027582] using wordTrace_append hprefix tailTrace_2027582
  have hstable : (prefixWord ++ tailWord_2027582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027582).length < 2 ^ (prefixWord ++ tailWord_2027582).sum := by decide
  have hdescent : baseEnd_2027582 < baseStart_2027582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027614 : List Nat := [4, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2027614 : Nat := 118140960795 + 2027614 * 2 ^ 59
def prefixEnd_2027614 : Nat := 4983230072969 + 3 ^ 40 * 2027614 * 2
def baseEnd_2027614 : Nat := 231364569730118929911151

theorem tailTrace_2027614 : CollatzResearch.WordTrace tailWord_2027614 prefixEnd_2027614 231364569730118929911151 := by
  unfold tailWord_2027614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9244144759538530218355237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49302105384205494497894597 9244144759538530218355237)
  ·
    refine ⟨1733277142413474415941607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9244144759538530218355237 1733277142413474415941607)
    ·
      refine ⟨2599915713620211623912411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733277142413474415941607 2599915713620211623912411)
      ·
        refine ⟨3899873570430317435868617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599915713620211623912411 3899873570430317435868617)
        ·
          refine ⟨2924905177822738076901463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3899873570430317435868617 2924905177822738076901463)
          ·
            refine ⟨4387357766734107115352195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2924905177822738076901463 4387357766734107115352195)
            ·
              refine ⟨6581036650101160673028293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4387357766734107115352195 6581036650101160673028293)
              ·
                refine ⟨1233944371893967626192805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6581036650101160673028293 1233944371893967626192805)
                ·
                  refine ⟨231364569730118929911151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1233944371893967626192805 231364569730118929911151)
                  ·
                    rfl

theorem cell22_2027614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2027614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027614 prefixEnd_2027614 := by exact prefixLift 2027614
  have htrace : WordTrace (prefixWord ++ tailWord_2027614) baseStart_2027614 baseEnd_2027614 := by
    simpa [prefixWord, tailWord_2027614, baseEnd_2027614] using wordTrace_append hprefix tailTrace_2027614
  have hstable : (prefixWord ++ tailWord_2027614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027614).length < 2 ^ (prefixWord ++ tailWord_2027614).sum := by decide
  have hdescent : baseEnd_2027614 < baseStart_2027614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027621 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_2027621 : Nat := 118140960795 + 2027621 * 2 ^ 59
def prefixEnd_2027621 : Nat := 4983230072969 + 3 ^ 40 * 2027621 * 2
def baseEnd_2027621 : Nat := 694096105433411104808431

theorem tailTrace_2027621 : CollatzResearch.WordTrace tailWord_2027621 prefixEnd_2027621 694096105433411104808431 := by
  unfold tailWord_2027621
  simp only [CollatzResearch.WordTrace]
  refine ⟨73953413387282881942346717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49302275591521921294897811 73953413387282881942346717)
  ·
    refine ⟨27732530020231080728380019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73953413387282881942346717 27732530020231080728380019)
    ·
      refine ⟨41598795030346621092570029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27732530020231080728380019 41598795030346621092570029)
      ·
        refine ⟨15599548136379982909713761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41598795030346621092570029 15599548136379982909713761)
        ·
          refine ⟨11699661102284987182285321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15599548136379982909713761 11699661102284987182285321)
          ·
            refine ⟨8774745826713740386713991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11699661102284987182285321 8774745826713740386713991)
            ·
              refine ⟨13162118740070610580070987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8774745826713740386713991 13162118740070610580070987)
              ·
                refine ⟨19743178110105915870106481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13162118740070610580070987 19743178110105915870106481)
                ·
                  refine ⟨14807383582579436902579861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19743178110105915870106481 14807383582579436902579861)
                  ·
                    refine ⟨694096105433411104808431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14807383582579436902579861 694096105433411104808431)
                    ·
                      rfl

theorem cell22_2027621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_2027621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027621 prefixEnd_2027621 := by exact prefixLift 2027621
  have htrace : WordTrace (prefixWord ++ tailWord_2027621) baseStart_2027621 baseEnd_2027621 := by
    simpa [prefixWord, tailWord_2027621, baseEnd_2027621] using wordTrace_append hprefix tailTrace_2027621
  have hstable : (prefixWord ++ tailWord_2027621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027621).length < 2 ^ (prefixWord ++ tailWord_2027621).sum := by decide
  have hdescent : baseEnd_2027621 < baseStart_2027621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027623 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 3, 3]
def baseStart_2027623 : Nat := 118140960795 + 2027623 * 2 ^ 59
def prefixEnd_2027623 : Nat := 4983230072969 + 3 ^ 40 * 2027623 * 2
def baseEnd_2027623 : Nat := 694096790074283766258425

theorem tailTrace_2027623 : CollatzResearch.WordTrace tailWord_2027623 prefixEnd_2027623 694096790074283766258425 := by
  unfold tailWord_2027623
  simp only [CollatzResearch.WordTrace]
  refine ⟨73953486333275636283919523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49302324222183757522613015 73953486333275636283919523)
  ·
    refine ⟨110930229499913454425879285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73953486333275636283919523 110930229499913454425879285)
    ·
      refine ⟨10399709015616886352426183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110930229499913454425879285 10399709015616886352426183)
      ·
        refine ⟨15599563523425329528639275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10399709015616886352426183 15599563523425329528639275)
        ·
          refine ⟨23399345285137994292958913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15599563523425329528639275 23399345285137994292958913)
          ·
            refine ⟨17549508963853495719719185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23399345285137994292958913 17549508963853495719719185)
            ·
              refine ⟨13162131722890121789789389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17549508963853495719719185 13162131722890121789789389)
              ·
                refine ⟨4935799396083795671171021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13162131722890121789789389 4935799396083795671171021)
                ·
                  refine ⟨1850924773531423376689133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4935799396083795671171021 1850924773531423376689133)
                  ·
                    refine ⟨694096790074283766258425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1850924773531423376689133 694096790074283766258425)
                    ·
                      rfl

theorem cell22_2027623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_2027623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027623 prefixEnd_2027623 := by exact prefixLift 2027623
  have htrace : WordTrace (prefixWord ++ tailWord_2027623) baseStart_2027623 baseEnd_2027623 := by
    simpa [prefixWord, tailWord_2027623, baseEnd_2027623] using wordTrace_append hprefix tailTrace_2027623
  have hstable : (prefixWord ++ tailWord_2027623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027623).length < 2 ^ (prefixWord ++ tailWord_2027623).sum := by decide
  have hdescent : baseEnd_2027623 < baseStart_2027623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027687 : List Nat := [1, 1, 6, 2, 2, 1, 3, 1, 5]
def baseStart_2027687 : Nat := 118140960795 + 2027687 * 2 ^ 59
def prefixEnd_2027687 : Nat := 4983230072969 + 3 ^ 40 * 2027687 * 2
def baseEnd_2027687 : Nat := 231372899527402977552743

theorem tailTrace_2027687 : CollatzResearch.WordTrace tailWord_2027687 prefixEnd_2027687 231372899527402977552743 := by
  unfold tailWord_2027687
  simp only [CollatzResearch.WordTrace]
  refine ⟨73955820605043775214249315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49303880403362516809499543 73955820605043775214249315)
  ·
    refine ⟨110933730907565662821373973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73955820605043775214249315 110933730907565662821373973)
    ·
      refine ⟨5200018636292140444751905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110933730907565662821373973 5200018636292140444751905)
      ·
        refine ⟨3900013977219105333563929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5200018636292140444751905 3900013977219105333563929)
        ·
          refine ⟨2925010482914329000172947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3900013977219105333563929 2925010482914329000172947)
          ·
            refine ⟨4387515724371493500259421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925010482914329000172947 4387515724371493500259421)
            ·
              refine ⟨1645318396639310062597283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4387515724371493500259421 1645318396639310062597283)
              ·
                refine ⟨2467977594958965093895925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645318396639310062597283 2467977594958965093895925)
                ·
                  refine ⟨231372899527402977552743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2467977594958965093895925 231372899527402977552743)
                  ·
                    rfl

theorem cell22_2027687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 5].length) (baseStart_2027687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027687 prefixEnd_2027687 := by exact prefixLift 2027687
  have htrace : WordTrace (prefixWord ++ tailWord_2027687) baseStart_2027687 baseEnd_2027687 := by
    simpa [prefixWord, tailWord_2027687, baseEnd_2027687] using wordTrace_append hprefix tailTrace_2027687
  have hstable : (prefixWord ++ tailWord_2027687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027687).length < 2 ^ (prefixWord ++ tailWord_2027687).sum := by decide
  have hdescent : baseEnd_2027687 < baseStart_2027687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027730 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_2027730 : Nat := 118140960795 + 2027730 * 2 ^ 59
def prefixEnd_2027730 : Nat := 4983230072969 + 3 ^ 40 * 2027730 * 2
def baseEnd_2027730 : Nat := 694133418360971153833097

theorem tailTrace_2027730 : CollatzResearch.WordTrace tailWord_2027730 prefixEnd_2027730 694133418360971153833097 := by
  unfold tailWord_2027730
  simp only [CollatzResearch.WordTrace]
  refine ⟨18489347235971998389516161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49304925962591995705376429 18489347235971998389516161)
  ·
    refine ⟨13867010426978998792137121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18489347235971998389516161 13867010426978998792137121)
    ·
      refine ⟨10400257820234249094102841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13867010426978998792137121 10400257820234249094102841)
      ·
        refine ⟨7800193365175686820577131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10400257820234249094102841 7800193365175686820577131)
        ·
          refine ⟨11700290047763530230865697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7800193365175686820577131 11700290047763530230865697)
          ·
            refine ⟨8775217535822647673149273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11700290047763530230865697 8775217535822647673149273)
            ·
              refine ⟨6581413151866985754861955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8775217535822647673149273 6581413151866985754861955)
              ·
                refine ⟨9872119727800478632292933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6581413151866985754861955 9872119727800478632292933)
                ·
                  refine ⟨1851022448962589743554925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9872119727800478632292933 1851022448962589743554925)
                  ·
                    refine ⟨694133418360971153833097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1851022448962589743554925 694133418360971153833097)
                    ·
                      rfl

theorem cell22_2027730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_2027730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027730 prefixEnd_2027730 := by exact prefixLift 2027730
  have htrace : WordTrace (prefixWord ++ tailWord_2027730) baseStart_2027730 baseEnd_2027730 := by
    simpa [prefixWord, tailWord_2027730, baseEnd_2027730] using wordTrace_append hprefix tailTrace_2027730
  have hstable : (prefixWord ++ tailWord_2027730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027730).length < 2 ^ (prefixWord ++ tailWord_2027730).sum := by decide
  have hdescent : baseEnd_2027730 < baseStart_2027730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027848 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 3, 5]
def baseStart_2027848 : Nat := 118140960795 + 2027848 * 2 ^ 59
def prefixEnd_2027848 : Nat := 4983230072969 + 3 ^ 40 * 2027848 * 2
def baseEnd_2027848 : Nat := 694173812172458179382735

theorem tailTrace_2027848 : CollatzResearch.WordTrace tailWord_2027848 prefixEnd_2027848 694173812172458179382735 := by
  unfold tailWord_2027848
  simp only [CollatzResearch.WordTrace]
  refine ⟨36980846378730249855430099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49307795171640333140573465 36980846378730249855430099)
  ·
    refine ⟨55471269568095374783145149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36980846378730249855430099 55471269568095374783145149)
    ·
      refine ⟨20801726088035765543679431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55471269568095374783145149 20801726088035765543679431)
      ·
        refine ⟨31202589132053648315519147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20801726088035765543679431 31202589132053648315519147)
        ·
          refine ⟨46803883698080472473278721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31202589132053648315519147 46803883698080472473278721)
          ·
            refine ⟨35102912773560354354959041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46803883698080472473278721 35102912773560354354959041)
            ·
              refine ⟨26327184580170265766219281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35102912773560354354959041 26327184580170265766219281)
              ·
                refine ⟨19745388435127699324664461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26327184580170265766219281 19745388435127699324664461)
                ·
                  refine ⟨7404520663172887246749173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19745388435127699324664461 7404520663172887246749173)
                  ·
                    refine ⟨694173812172458179382735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7404520663172887246749173 694173812172458179382735)
                    ·
                      rfl

theorem cell22_2027848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_2027848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027848 prefixEnd_2027848 := by exact prefixLift 2027848
  have htrace : WordTrace (prefixWord ++ tailWord_2027848) baseStart_2027848 baseEnd_2027848 := by
    simpa [prefixWord, tailWord_2027848, baseEnd_2027848] using wordTrace_append hprefix tailTrace_2027848
  have hstable : (prefixWord ++ tailWord_2027848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027848).length < 2 ^ (prefixWord ++ tailWord_2027848).sum := by decide
  have hdescent : baseEnd_2027848 < baseStart_2027848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027863 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 3, 6]
def baseStart_2027863 : Nat := 118140960795 + 2027863 * 2 ^ 59
def prefixEnd_2027863 : Nat := 4983230072969 + 3 ^ 40 * 2027863 * 2
def baseEnd_2027863 : Nat := 694178946979003140257689

theorem tailTrace_2027863 : CollatzResearch.WordTrace tailWord_2027863 prefixEnd_2027863 694178946979003140257689 := by
  unfold tailWord_2027863
  simp only [CollatzResearch.WordTrace]
  refine ⟨73962239852406157272656243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49308159901604104848437495 73962239852406157272656243)
  ·
    refine ⟨110943359778609235908984365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73962239852406157272656243 110943359778609235908984365)
    ·
      refine ⟨41603759916978463465869137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110943359778609235908984365 41603759916978463465869137)
      ·
        refine ⟨31202819937733847599401853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41603759916978463465869137 31202819937733847599401853)
        ·
          refine ⟨11701057476650192849775695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31202819937733847599401853 11701057476650192849775695)
          ·
            refine ⟨17551586214975289274663543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11701057476650192849775695 17551586214975289274663543)
            ·
              refine ⟨26327379322462933911995315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17551586214975289274663543 26327379322462933911995315)
              ·
                refine ⟨39491068983694400867992973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26327379322462933911995315 39491068983694400867992973)
                ·
                  refine ⟨14809150868885400325497365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39491068983694400867992973 14809150868885400325497365)
                  ·
                    refine ⟨694178946979003140257689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14809150868885400325497365 694178946979003140257689)
                    ·
                      rfl

theorem cell22_2027863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_2027863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027863 prefixEnd_2027863 := by exact prefixLift 2027863
  have htrace : WordTrace (prefixWord ++ tailWord_2027863) baseStart_2027863 baseEnd_2027863 := by
    simpa [prefixWord, tailWord_2027863, baseEnd_2027863] using wordTrace_append hprefix tailTrace_2027863
  have hstable : (prefixWord ++ tailWord_2027863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027863).length < 2 ^ (prefixWord ++ tailWord_2027863).sum := by decide
  have hdescent : baseEnd_2027863 < baseStart_2027863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027880 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 1, 6]
def baseStart_2027880 : Nat := 118140960795 + 2027880 * 2 ^ 59
def prefixEnd_2027880 : Nat := 4983230072969 + 3 ^ 40 * 2027880 * 2
def baseEnd_2027880 : Nat := 694184766426420762582637

theorem tailTrace_2027880 : CollatzResearch.WordTrace tailWord_2027880 prefixEnd_2027880 694184766426420762582637 := by
  unfold tailWord_2027880
  simp only [CollatzResearch.WordTrace]
  refine ⟨36981429946672284588012547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49308573262229712784016729 36981429946672284588012547)
  ·
    refine ⟨55472144920008426882018821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36981429946672284588012547 55472144920008426882018821)
    ·
      refine ⟨10401027172501580040378529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55472144920008426882018821 10401027172501580040378529)
      ·
        refine ⟨7800770379376185030283897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10401027172501580040378529 7800770379376185030283897)
        ·
          refine ⟨5850577784532138772712923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7800770379376185030283897 5850577784532138772712923)
          ·
            refine ⟨8775866676798208159069385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5850577784532138772712923 8775866676798208159069385)
            ·
              refine ⟨6581900007598656119302039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8775866676798208159069385 6581900007598656119302039)
              ·
                refine ⟨9872850011397984178953059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6581900007598656119302039 9872850011397984178953059)
                ·
                  refine ⟨14809275017096976268429589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9872850011397984178953059 14809275017096976268429589)
                  ·
                    refine ⟨694184766426420762582637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14809275017096976268429589 694184766426420762582637)
                    ·
                      rfl

theorem cell22_2027880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_2027880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027880 prefixEnd_2027880 := by exact prefixLift 2027880
  have htrace : WordTrace (prefixWord ++ tailWord_2027880) baseStart_2027880 baseEnd_2027880 := by
    simpa [prefixWord, tailWord_2027880, baseEnd_2027880] using wordTrace_append hprefix tailTrace_2027880
  have hstable : (prefixWord ++ tailWord_2027880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027880).length < 2 ^ (prefixWord ++ tailWord_2027880).sum := by decide
  have hdescent : baseEnd_2027880 < baseStart_2027880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027882 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 4, 3]
def baseStart_2027882 : Nat := 118140960795 + 2027882 * 2 ^ 59
def prefixEnd_2027882 : Nat := 4983230072969 + 3 ^ 40 * 2027882 * 2
def baseEnd_2027882 : Nat := 694185451067293424032631

theorem tailTrace_2027882 : CollatzResearch.WordTrace tailWord_2027882 prefixEnd_2027882 694185451067293424032631 := by
  unfold tailWord_2027882
  simp only [CollatzResearch.WordTrace]
  refine ⟨18490733209834330879399475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49308621892891549011731933 18490733209834330879399475)
  ·
    refine ⟨27736099814751496319099213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18490733209834330879399475 27736099814751496319099213)
    ·
      refine ⟨10401037430531811119662205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27736099814751496319099213 10401037430531811119662205)
      ·
        refine ⟨3900389036449429169873327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10401037430531811119662205 3900389036449429169873327)
        ·
          refine ⟨5850583554674143754809991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900389036449429169873327 5850583554674143754809991)
          ·
            refine ⟨8775875332011215632214987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5850583554674143754809991 8775875332011215632214987)
            ·
              refine ⟨13163812998016823448322481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8775875332011215632214987 13163812998016823448322481)
              ·
                refine ⟨9872859748512617586241861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13163812998016823448322481 9872859748512617586241861)
                ·
                  refine ⟨1851161202846115797420349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9872859748512617586241861 1851161202846115797420349)
                  ·
                    refine ⟨694185451067293424032631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1851161202846115797420349 694185451067293424032631)
                    ·
                      rfl

theorem cell22_2027882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_2027882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027882 prefixEnd_2027882 := by exact prefixLift 2027882
  have htrace : WordTrace (prefixWord ++ tailWord_2027882) baseStart_2027882 baseEnd_2027882 := by
    simpa [prefixWord, tailWord_2027882, baseEnd_2027882] using wordTrace_append hprefix tailTrace_2027882
  have hstable : (prefixWord ++ tailWord_2027882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027882).length < 2 ^ (prefixWord ++ tailWord_2027882).sum := by decide
  have hdescent : baseEnd_2027882 < baseStart_2027882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027884 : List Nat := [2, 2, 1, 1, 6, 2, 1, 3, 4]
def baseStart_2027884 : Nat := 118140960795 + 2027884 * 2 ^ 59
def prefixEnd_2027884 : Nat := 4983230072969 + 3 ^ 40 * 2027884 * 2
def baseEnd_2027884 : Nat := 231395378569388695160875

theorem tailTrace_2027884 : CollatzResearch.WordTrace tailWord_2027884 prefixEnd_2027884 231395378569388695160875 := by
  unfold tailWord_2027884
  simp only [CollatzResearch.WordTrace]
  refine ⟨36981502892665038929585353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49308670523553385239447137 36981502892665038929585353)
  ·
    refine ⟨27736127169498779197189015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36981502892665038929585353 27736127169498779197189015)
    ·
      refine ⟨41604190754248168795783523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27736127169498779197189015 41604190754248168795783523)
      ·
        refine ⟨62406286131372253193675285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41604190754248168795783523 62406286131372253193675285)
        ·
          refine ⟨2925294662408074368453529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62406286131372253193675285 2925294662408074368453529)
          ·
            refine ⟨2193970996806055776340147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2925294662408074368453529 2193970996806055776340147)
            ·
              refine ⟨3290956495209083664510221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193970996806055776340147 3290956495209083664510221)
              ·
                refine ⟨1234108685703406374191333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3290956495209083664510221 1234108685703406374191333)
                ·
                  refine ⟨231395378569388695160875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1234108685703406374191333 231395378569388695160875)
                  ·
                    rfl

theorem cell22_2027884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_2027884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027884 prefixEnd_2027884 := by exact prefixLift 2027884
  have htrace : WordTrace (prefixWord ++ tailWord_2027884) baseStart_2027884 baseEnd_2027884 := by
    simpa [prefixWord, tailWord_2027884, baseEnd_2027884] using wordTrace_append hprefix tailTrace_2027884
  have hstable : (prefixWord ++ tailWord_2027884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027884).length < 2 ^ (prefixWord ++ tailWord_2027884).sum := by decide
  have hdescent : baseEnd_2027884 < baseStart_2027884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027961 : List Nat := [1, 2, 1, 4, 3, 1, 4, 2, 1, 3]
def baseStart_2027961 : Nat := 118140960795 + 2027961 * 2 ^ 59
def prefixEnd_2027961 : Nat := 4983230072969 + 3 ^ 40 * 2027961 * 2
def baseEnd_2027961 : Nat := 694212494381763551307389

theorem tailTrace_2027961 : CollatzResearch.WordTrace tailWord_2027961 prefixEnd_2027961 694212494381763551307389 := by
  unfold tailWord_2027961
  simp only [CollatzResearch.WordTrace]
  refine ⟨73965814206051120009723737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49310542804034080006482491 73965814206051120009723737)
  ·
    refine ⟨55474360654538340007292803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73965814206051120009723737 55474360654538340007292803)
    ·
      refine ⟨83211540981807510010939205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55474360654538340007292803 83211540981807510010939205)
      ·
        refine ⟨15602163934088908127051101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83211540981807510010939205 15602163934088908127051101)
        ·
          refine ⟨5850811475283340547644163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15602163934088908127051101 5850811475283340547644163)
          ·
            refine ⟨8776217212925010821466245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5850811475283340547644163 8776217212925010821466245)
            ·
              refine ⟨1645540727423439529024921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8776217212925010821466245 1645540727423439529024921)
              ·
                refine ⟨1234155545567579646768691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1645540727423439529024921 1234155545567579646768691)
                ·
                  refine ⟨1851233318351369470153037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1234155545567579646768691 1851233318351369470153037)
                  ·
                    refine ⟨694212494381763551307389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1851233318351369470153037 694212494381763551307389)
                    ·
                      rfl

theorem cell22_2027961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 1, 3].length) (baseStart_2027961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2027961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2027961 prefixEnd_2027961 := by exact prefixLift 2027961
  have htrace : WordTrace (prefixWord ++ tailWord_2027961) baseStart_2027961 baseEnd_2027961 := by
    simpa [prefixWord, tailWord_2027961, baseEnd_2027961] using wordTrace_append hprefix tailTrace_2027961
  have hstable : (prefixWord ++ tailWord_2027961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027961).length < 2 ^ (prefixWord ++ tailWord_2027961).sum := by decide
  have hdescent : baseEnd_2027961 < baseStart_2027961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028000 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 1, 5]
def baseStart_2028000 : Nat := 118140960795 + 2028000 * 2 ^ 59
def prefixEnd_2028000 : Nat := 4983230072969 + 3 ^ 40 * 2028000 * 2
def baseEnd_2028000 : Nat := 694225844878780449582269

theorem tailTrace_2028000 : CollatzResearch.WordTrace tailWord_2028000 prefixEnd_2028000 694225844878780449582269 := by
  unfold tailWord_2028000
  simp only [CollatzResearch.WordTrace]
  refine ⟨36983618326454914835196727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49311491101939886446928969 36983618326454914835196727)
  ·
    refine ⟨55475427489682372252795091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36983618326454914835196727 55475427489682372252795091)
    ·
      refine ⟨83213141234523558379192637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55475427489682372252795091 83213141234523558379192637)
      ·
        refine ⟨31204927962946334392197239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83213141234523558379192637 31204927962946334392197239)
        ·
          refine ⟨46807391944419501588295859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31204927962946334392197239 46807391944419501588295859)
          ·
            refine ⟨70211087916629252382443789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46807391944419501588295859 70211087916629252382443789)
            ·
              refine ⟨26329157968735969643416421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70211087916629252382443789 26329157968735969643416421)
              ·
                refine ⟨4936717119137994308140579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26329157968735969643416421 4936717119137994308140579)
                ·
                  refine ⟨7405075678706991462210869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4936717119137994308140579 7405075678706991462210869)
                  ·
                    refine ⟨694225844878780449582269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7405075678706991462210869 694225844878780449582269)
                    ·
                      rfl

theorem cell22_2028000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_2028000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028000 prefixEnd_2028000 := by exact prefixLift 2028000
  have htrace : WordTrace (prefixWord ++ tailWord_2028000) baseStart_2028000 baseEnd_2028000 := by
    simpa [prefixWord, tailWord_2028000, baseEnd_2028000] using wordTrace_append hprefix tailTrace_2028000
  have hstable : (prefixWord ++ tailWord_2028000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028000).length < 2 ^ (prefixWord ++ tailWord_2028000).sum := by decide
  have hdescent : baseEnd_2028000 < baseStart_2028000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028015 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 4, 4]
def baseStart_2028015 : Nat := 118140960795 + 2028015 * 2 ^ 59
def prefixEnd_2028015 : Nat := 4983230072969 + 3 ^ 40 * 2028015 * 2
def baseEnd_2028015 : Nat := 694230979685325410457223

theorem tailTrace_2028015 : CollatzResearch.WordTrace tailWord_2028015 prefixEnd_2028015 694230979685325410457223 := by
  unfold tailWord_2028015
  simp only [CollatzResearch.WordTrace]
  refine ⟨73967783747855487232189499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49311855831903658154792999 73967783747855487232189499)
  ·
    refine ⟨110951675621783230848284249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73967783747855487232189499 110951675621783230848284249)
    ·
      refine ⟨83213756716337423136213187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110951675621783230848284249 83213756716337423136213187)
      ·
        refine ⟨124820635074506134704319781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83213756716337423136213187 124820635074506134704319781)
        ·
          refine ⟨23403869076469900257059959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124820635074506134704319781 23403869076469900257059959)
          ·
            refine ⟨35105803614704850385589939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23403869076469900257059959 35105803614704850385589939)
            ·
              refine ⟨52658705422057275578384909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35105803614704850385589939 52658705422057275578384909)
              ·
                refine ⟨19747014533271478341894341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52658705422057275578384909 19747014533271478341894341)
                ·
                  refine ⟨3702565224988402189105189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19747014533271478341894341 3702565224988402189105189)
                  ·
                    refine ⟨694230979685325410457223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3702565224988402189105189 694230979685325410457223)
                    ·
                      rfl

theorem cell22_2028015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_2028015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028015 prefixEnd_2028015 := by exact prefixLift 2028015
  have htrace : WordTrace (prefixWord ++ tailWord_2028015) baseStart_2028015 baseEnd_2028015 := by
    simpa [prefixWord, tailWord_2028015, baseEnd_2028015] using wordTrace_append hprefix tailTrace_2028015
  have hstable : (prefixWord ++ tailWord_2028015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028015).length < 2 ^ (prefixWord ++ tailWord_2028015).sum := by decide
  have hdescent : baseEnd_2028015 < baseStart_2028015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028017 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 4, 3]
def baseStart_2028017 : Nat := 118140960795 + 2028017 * 2 ^ 59
def prefixEnd_2028017 : Nat := 4983230072969 + 3 ^ 40 * 2028017 * 2
def baseEnd_2028017 : Nat := 694231664326198071907217

theorem tailTrace_2028017 : CollatzResearch.WordTrace tailWord_2028017 prefixEnd_2028017 694231664326198071907217 := by
  unfold tailWord_2028017
  simp only [CollatzResearch.WordTrace]
  refine ⟨73967856693848241573762305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49311904462565494382508203 73967856693848241573762305)
  ·
    refine ⟨55475892520386181180321729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73967856693848241573762305 55475892520386181180321729)
    ·
      refine ⟨41606919390289635885241297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55475892520386181180321729 41606919390289635885241297)
      ·
        refine ⟨31205189542717226913930973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41606919390289635885241297 31205189542717226913930973)
        ·
          refine ⟨11701946078518960092724115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31205189542717226913930973 11701946078518960092724115)
          ·
            refine ⟨17552919117778440139086173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11701946078518960092724115 17552919117778440139086173)
            ·
              refine ⟨6582344669166915052157315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17552919117778440139086173 6582344669166915052157315)
              ·
                refine ⟨9873517003750372578235973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6582344669166915052157315 9873517003750372578235973)
                ·
                  refine ⟨1851284438203194858419245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9873517003750372578235973 1851284438203194858419245)
                  ·
                    refine ⟨694231664326198071907217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1851284438203194858419245 694231664326198071907217)
                    ·
                      rfl

theorem cell22_2028017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_2028017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028017 prefixEnd_2028017 := by exact prefixLift 2028017
  have htrace : WordTrace (prefixWord ++ tailWord_2028017) baseStart_2028017 baseEnd_2028017 := by
    simpa [prefixWord, tailWord_2028017, baseEnd_2028017] using wordTrace_append hprefix tailTrace_2028017
  have hstable : (prefixWord ++ tailWord_2028017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028017).length < 2 ^ (prefixWord ++ tailWord_2028017).sum := by decide
  have hdescent : baseEnd_2028017 < baseStart_2028017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028038 : List Nat := [6, 2, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2028038 : Nat := 118140960795 + 2028038 * 2 ^ 59
def prefixEnd_2028038 : Nat := 4983230072969 + 3 ^ 40 * 2028038 * 2
def baseEnd_2028038 : Nat := 694238853055361017132153

theorem tailTrace_2028038 : CollatzResearch.WordTrace tailWord_2028038 prefixEnd_2028038 694238853055361017132153 := by
  unfold tailWord_2028038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311519457086630067508649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49312415084514774773517845 2311519457086630067508649)
  ·
    refine ⟨1733639592814972550631487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2311519457086630067508649 1733639592814972550631487)
    ·
      refine ⟨2600459389222458825947231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733639592814972550631487 2600459389222458825947231)
      ·
        refine ⟨3900689083833688238920847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2600459389222458825947231 3900689083833688238920847)
        ·
          refine ⟨5851033625750532358381271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900689083833688238920847 5851033625750532358381271)
          ·
            refine ⟨8776550438625798537571907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5851033625750532358381271 8776550438625798537571907)
            ·
              refine ⟨13164825657938697806357861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8776550438625798537571907 13164825657938697806357861)
              ·
                refine ⟨2468404810863505838692099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13164825657938697806357861 2468404810863505838692099)
                ·
                  refine ⟨3702607216295258758038149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468404810863505838692099 3702607216295258758038149)
                  ·
                    refine ⟨694238853055361017132153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3702607216295258758038149 694238853055361017132153)
                    ·
                      rfl

theorem cell22_2028038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2028038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028038 prefixEnd_2028038 := by exact prefixLift 2028038
  have htrace : WordTrace (prefixWord ++ tailWord_2028038) baseStart_2028038 baseEnd_2028038 := by
    simpa [prefixWord, tailWord_2028038, baseEnd_2028038] using wordTrace_append hprefix tailTrace_2028038
  have hstable : (prefixWord ++ tailWord_2028038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028038).length < 2 ^ (prefixWord ++ tailWord_2028038).sum := by decide
  have hdescent : baseEnd_2028038 < baseStart_2028038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028064 : List Nat := [2, 1, 1, 6, 3, 1, 8]
def baseStart_2028064 : Nat := 118140960795 + 2028064 * 2 ^ 59
def prefixEnd_2028064 : Nat := 4983230072969 + 3 ^ 40 * 2028064 * 2
def baseEnd_2028064 : Nat := 25712879755063170962299

theorem tailTrace_2028064 : CollatzResearch.WordTrace tailWord_2028064 prefixEnd_2028064 25712879755063170962299 := by
  unfold tailWord_2028064
  simp only [CollatzResearch.WordTrace]
  refine ⟨36984785462338984300361623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49313047283118645733815497 36984785462338984300361623)
  ·
    refine ⟨55477178193508476450542435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36984785462338984300361623 55477178193508476450542435)
    ·
      refine ⟨83215767290262714675813653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55477178193508476450542435 83215767290262714675813653)
      ·
        refine ⟨3900739091731064750428765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83215767290262714675813653 3900739091731064750428765)
        ·
          refine ⟨1462777159399149281410787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3900739091731064750428765 1462777159399149281410787)
          ·
            refine ⟨2194165739098723922116181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462777159399149281410787 2194165739098723922116181)
            ·
              refine ⟨25712879755063170962299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2194165739098723922116181 25712879755063170962299)
              ·
                rfl

theorem cell22_2028064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 8].length) (baseStart_2028064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028064 prefixEnd_2028064 := by exact prefixLift 2028064
  have htrace : WordTrace (prefixWord ++ tailWord_2028064) baseStart_2028064 baseEnd_2028064 := by
    simpa [prefixWord, tailWord_2028064, baseEnd_2028064] using wordTrace_append hprefix tailTrace_2028064
  have hstable : (prefixWord ++ tailWord_2028064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028064).length < 2 ^ (prefixWord ++ tailWord_2028064).sum := by decide
  have hdescent : baseEnd_2028064 < baseStart_2028064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028130 : List Nat := [3, 3, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_2028130 : Nat := 118140960795 + 2028130 * 2 ^ 59
def prefixEnd_2028130 : Nat := 4983230072969 + 3 ^ 40 * 2028130 * 2
def baseEnd_2028130 : Nat := 694270346535503443831871

theorem tailTrace_2028130 : CollatzResearch.WordTrace tailWord_2028130 prefixEnd_2028130 694270346535503443831871 := by
  unfold tailWord_2028130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18492994535609715468156461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49314652094959241248417229 18492994535609715468156461)
  ·
    refine ⟨6934872950853643300558673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18492994535609715468156461 6934872950853643300558673)
    ·
      refine ⟨5201154713140232475419005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6934872950853643300558673 5201154713140232475419005)
      ·
        refine ⟨1950433017427587178282127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5201154713140232475419005 1950433017427587178282127)
        ·
          refine ⟨2925649526141380767423191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950433017427587178282127 2925649526141380767423191)
          ·
            refine ⟨4388474289212071151134787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925649526141380767423191 4388474289212071151134787)
            ·
              refine ⟨6582711433818106726702181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388474289212071151134787 6582711433818106726702181)
              ·
                refine ⟨1234258393840895011256659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6582711433818106726702181 1234258393840895011256659)
                ·
                  refine ⟨1851387590761342516884989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1234258393840895011256659 1851387590761342516884989)
                  ·
                    refine ⟨694270346535503443831871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1851387590761342516884989 694270346535503443831871)
                    ·
                      rfl

theorem cell22_2028130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_2028130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028130 prefixEnd_2028130 := by exact prefixLift 2028130
  have htrace : WordTrace (prefixWord ++ tailWord_2028130) baseStart_2028130 baseEnd_2028130 := by
    simpa [prefixWord, tailWord_2028130, baseEnd_2028130] using wordTrace_append hprefix tailTrace_2028130
  have hstable : (prefixWord ++ tailWord_2028130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028130).length < 2 ^ (prefixWord ++ tailWord_2028130).sum := by decide
  have hdescent : baseEnd_2028130 < baseStart_2028130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028167 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 1, 6]
def baseStart_2028167 : Nat := 118140960795 + 2028167 * 2 ^ 59
def prefixEnd_2028167 : Nat := 4983230072969 + 3 ^ 40 * 2028167 * 2
def baseEnd_2028167 : Nat := 694283012391647680656757

theorem tailTrace_2028167 : CollatzResearch.WordTrace tailWord_2028167 prefixEnd_2028167 694283012391647680656757 := by
  unfold tailWord_2028167
  simp only [CollatzResearch.WordTrace]
  refine ⟨73973327643304817191722755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49315551762203211461148503 73973327643304817191722755)
  ·
    refine ⟨110959991464957225787584133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73973327643304817191722755 110959991464957225787584133)
    ·
      refine ⟨20804998399679479835172025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110959991464957225787584133 20804998399679479835172025)
      ·
        refine ⟨15603748799759609876379019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20804998399679479835172025 15603748799759609876379019)
        ·
          refine ⟨23405623199639414814568529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15603748799759609876379019 23405623199639414814568529)
          ·
            refine ⟨17554217399729561110926397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23405623199639414814568529 17554217399729561110926397)
            ·
              refine ⟨6582831524898585416597399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17554217399729561110926397 6582831524898585416597399)
              ·
                refine ⟨9874247287347878124896099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6582831524898585416597399 9874247287347878124896099)
                ·
                  refine ⟨14811370931021817187344149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9874247287347878124896099 14811370931021817187344149)
                  ·
                    refine ⟨694283012391647680656757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14811370931021817187344149 694283012391647680656757)
                    ·
                      rfl

theorem cell22_2028167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_2028167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028167 prefixEnd_2028167 := by exact prefixLift 2028167
  have htrace : WordTrace (prefixWord ++ tailWord_2028167) baseStart_2028167 baseEnd_2028167 := by
    simpa [prefixWord, tailWord_2028167, baseEnd_2028167] using wordTrace_append hprefix tailTrace_2028167
  have hstable : (prefixWord ++ tailWord_2028167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028167).length < 2 ^ (prefixWord ++ tailWord_2028167).sum := by decide
  have hdescent : baseEnd_2028167 < baseStart_2028167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028231 : List Nat := [1, 1, 4, 1, 1, 1, 2, 7, 1, 3]
def baseStart_2028231 : Nat := 118140960795 + 2028231 * 2 ^ 59
def prefixEnd_2028231 : Nat := 4983230072969 + 3 ^ 40 * 2028231 * 2
def baseEnd_2028231 : Nat := 694304920899572847056561

theorem tailTrace_2028231 : CollatzResearch.WordTrace tailWord_2028231 prefixEnd_2028231 694304920899572847056561 := by
  unfold tailWord_2028231
  simp only [CollatzResearch.WordTrace]
  refine ⟨73975661915072956122052547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49317107943381970748035031 73975661915072956122052547)
  ·
    refine ⟨110963492872609434183078821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73975661915072956122052547 110963492872609434183078821)
    ·
      refine ⟨20805654913614268909327279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110963492872609434183078821 20805654913614268909327279)
      ·
        refine ⟨31208482370421403363990919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20805654913614268909327279 31208482370421403363990919)
        ·
          refine ⟨46812723555632105045986379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31208482370421403363990919 46812723555632105045986379)
          ·
            refine ⟨70219085333448157568979569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46812723555632105045986379 70219085333448157568979569)
            ·
              refine ⟨52664314000086118176734677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70219085333448157568979569 52664314000086118176734677)
              ·
                refine ⟨1234319859377018394767219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52664314000086118176734677 1234319859377018394767219)
                ·
                  refine ⟨1851479789065527592150829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1234319859377018394767219 1851479789065527592150829)
                  ·
                    refine ⟨694304920899572847056561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1851479789065527592150829 694304920899572847056561)
                    ·
                      rfl

theorem cell22_2028231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_2028231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028231 prefixEnd_2028231 := by exact prefixLift 2028231
  have htrace : WordTrace (prefixWord ++ tailWord_2028231) baseStart_2028231 baseEnd_2028231 := by
    simpa [prefixWord, tailWord_2028231, baseEnd_2028231] using wordTrace_append hprefix tailTrace_2028231
  have hstable : (prefixWord ++ tailWord_2028231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028231).length < 2 ^ (prefixWord ++ tailWord_2028231).sum := by decide
  have hdescent : baseEnd_2028231 < baseStart_2028231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028261 : List Nat := [1, 3, 1, 4, 1, 2, 4, 1, 5]
def baseStart_2028261 : Nat := 118140960795 + 2028261 * 2 ^ 59
def prefixEnd_2028261 : Nat := 4983230072969 + 3 ^ 40 * 2028261 * 2
def baseEnd_2028261 : Nat := 231438396837554256268823

theorem tailTrace_2028261 : CollatzResearch.WordTrace tailWord_2028261 prefixEnd_2028261 231438396837554256268823 := by
  unfold tailWord_2028261
  simp only [CollatzResearch.WordTrace]
  refine ⟨73976756104964271245644637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49317837403309514163763091 73976756104964271245644637)
  ·
    refine ⟨27741283539361601717116739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73976756104964271245644637 27741283539361601717116739)
    ·
      refine ⟨41611925309042402575675109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27741283539361601717116739 41611925309042402575675109)
      ·
        refine ⟨7802235995445450482939083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41611925309042402575675109 7802235995445450482939083)
        ·
          refine ⟨11703353993168175724408625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7802235995445450482939083 11703353993168175724408625)
          ·
            refine ⟨8777515494876131793306469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11703353993168175724408625 8777515494876131793306469)
            ·
              refine ⟨1645784155289274711244963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8777515494876131793306469 1645784155289274711244963)
              ·
                refine ⟨2468676232933912066867445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645784155289274711244963 2468676232933912066867445)
                ·
                  refine ⟨231438396837554256268823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2468676232933912066867445 231438396837554256268823)
                  ·
                    rfl

theorem cell22_2028261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_2028261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028261 prefixEnd_2028261 := by exact prefixLift 2028261
  have htrace : WordTrace (prefixWord ++ tailWord_2028261) baseStart_2028261 baseEnd_2028261 := by
    simpa [prefixWord, tailWord_2028261, baseEnd_2028261] using wordTrace_append hprefix tailTrace_2028261
  have hstable : (prefixWord ++ tailWord_2028261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028261).length < 2 ^ (prefixWord ++ tailWord_2028261).sum := by decide
  have hdescent : baseEnd_2028261 < baseStart_2028261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028272 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 8]
def baseStart_2028272 : Nat := 118140960795 + 2028272 * 2 ^ 59
def prefixEnd_2028272 : Nat := 4983230072969 + 3 ^ 40 * 2028272 * 2
def baseEnd_2028272 : Nat := 231439652012487468927145

theorem tailTrace_2028272 : CollatzResearch.WordTrace tailWord_2028272 prefixEnd_2028272 231439652012487468927145 := by
  unfold tailWord_2028272
  simp only [CollatzResearch.WordTrace]
  refine ⟨36988578653962210062147535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49318104871949613416196713 36988578653962210062147535)
  ·
    refine ⟨55482867980943315093221303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36988578653962210062147535 55482867980943315093221303)
    ·
      refine ⟨83224301971414972639831955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55482867980943315093221303 83224301971414972639831955)
      ·
        refine ⟨124836452957122458959747933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83224301971414972639831955 124836452957122458959747933)
        ·
          refine ⟨46813669858920922109905475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124836452957122458959747933 46813669858920922109905475)
          ·
            refine ⟨70220504788381383164858213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46813669858920922109905475 70220504788381383164858213)
            ·
              refine ⟨13166344647821509343410915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70220504788381383164858213 13166344647821509343410915)
              ·
                refine ⟨19749516971732264015116373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13166344647821509343410915 19749516971732264015116373)
                ·
                  refine ⟨231439652012487468927145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19749516971732264015116373 231439652012487468927145)
                  ·
                    rfl

theorem cell22_2028272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_2028272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028272 prefixEnd_2028272 := by exact prefixLift 2028272
  have htrace : WordTrace (prefixWord ++ tailWord_2028272) baseStart_2028272 baseEnd_2028272 := by
    simpa [prefixWord, tailWord_2028272, baseEnd_2028272] using wordTrace_append hprefix tailTrace_2028272
  have hstable : (prefixWord ++ tailWord_2028272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028272).length < 2 ^ (prefixWord ++ tailWord_2028272).sum := by decide
  have hdescent : baseEnd_2028272 < baseStart_2028272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028321 : List Nat := [1, 2, 3, 2, 1, 2, 1, 5, 2, 3]
def baseStart_2028321 : Nat := 118140960795 + 2028321 * 2 ^ 59
def prefixEnd_2028321 : Nat := 4983230072969 + 3 ^ 40 * 2028321 * 2
def baseEnd_2028321 : Nat := 694335729738842612306285

theorem tailTrace_2028321 : CollatzResearch.WordTrace tailWord_2028321 prefixEnd_2028321 694335729738842612306285 := by
  unfold tailWord_2028321
  simp only [CollatzResearch.WordTrace]
  refine ⟨73978944484746901492828817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49319296323164600995219211 73978944484746901492828817)
  ·
    refine ⟨55484208363560176119621613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73978944484746901492828817 55484208363560176119621613)
    ·
      refine ⟨20806578136335066044858105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55484208363560176119621613 20806578136335066044858105)
      ·
        refine ⟨15604933602251299533643579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20806578136335066044858105 15604933602251299533643579)
        ·
          refine ⟨23407400403376949300465369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15604933602251299533643579 23407400403376949300465369)
          ·
            refine ⟨17555550302532711975349027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23407400403376949300465369 17555550302532711975349027)
            ·
              refine ⟨26333325453799067963023541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17555550302532711975349027 26333325453799067963023541)
              ·
                refine ⟨2468749261293662621533457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26333325453799067963023541 2468749261293662621533457)
                ·
                  refine ⟨1851561945970246966150093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2468749261293662621533457 1851561945970246966150093)
                  ·
                    refine ⟨694335729738842612306285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1851561945970246966150093 694335729738842612306285)
                    ·
                      rfl

theorem cell22_2028321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_2028321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028321 prefixEnd_2028321 := by exact prefixLift 2028321
  have htrace : WordTrace (prefixWord ++ tailWord_2028321) baseStart_2028321 baseEnd_2028321 := by
    simpa [prefixWord, tailWord_2028321, baseEnd_2028321] using wordTrace_append hprefix tailTrace_2028321
  have hstable : (prefixWord ++ tailWord_2028321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028321).length < 2 ^ (prefixWord ++ tailWord_2028321).sum := by decide
  have hdescent : baseEnd_2028321 < baseStart_2028321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028340 : List Nat := [2, 5, 1, 1, 3, 1, 2, 3, 4]
def baseStart_2028340 : Nat := 118140960795 + 2028340 * 2 ^ 59
def prefixEnd_2028340 : Nat := 4983230072969 + 3 ^ 40 * 2028340 * 2
def baseEnd_2028340 : Nat := 231447411275710965360409

theorem tailTrace_2028340 : CollatzResearch.WordTrace tailWord_2028340 prefixEnd_2028340 231447411275710965360409 := by
  unfold tailWord_2028340
  simp only [CollatzResearch.WordTrace]
  refine ⟨36989818735839033868885237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49319758314452045158513649 36989818735839033868885237)
  ·
    refine ⟨3467795506484909425207991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36989818735839033868885237 3467795506484909425207991)
    ·
      refine ⟨5201693259727364137811987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3467795506484909425207991 5201693259727364137811987)
      ·
        refine ⟨7802539889591046206717981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5201693259727364137811987 7802539889591046206717981)
        ·
          refine ⟨2925952458596642327519243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7802539889591046206717981 2925952458596642327519243)
          ·
            refine ⟨4388928687894963491278865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925952458596642327519243 4388928687894963491278865)
            ·
              refine ⟨3291696515921222618459149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4388928687894963491278865 3291696515921222618459149)
              ·
                refine ⟨1234386193470458481922181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3291696515921222618459149 1234386193470458481922181)
                ·
                  refine ⟨231447411275710965360409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1234386193470458481922181 231447411275710965360409)
                  ·
                    rfl

theorem cell22_2028340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_2028340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028340 prefixEnd_2028340 := by exact prefixLift 2028340
  have htrace : WordTrace (prefixWord ++ tailWord_2028340) baseStart_2028340 baseEnd_2028340 := by
    simpa [prefixWord, tailWord_2028340, baseEnd_2028340] using wordTrace_append hprefix tailTrace_2028340
  have hstable : (prefixWord ++ tailWord_2028340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028340).length < 2 ^ (prefixWord ++ tailWord_2028340).sum := by decide
  have hdescent : baseEnd_2028340 < baseStart_2028340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028342 : List Nat := [5, 1, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_2028342 : Nat := 118140960795 + 2028342 * 2 ^ 59
def prefixEnd_2028342 : Nat := 4983230072969 + 3 ^ 40 * 2028342 * 2
def baseEnd_2028342 : Nat := 694342918468005557531221

theorem tailTrace_2028342 : CollatzResearch.WordTrace tailWord_2028342 prefixEnd_2028342 694342918468005557531221 := by
  unfold tailWord_2028342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4623731901104426379958955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49319806945113881386228853 4623731901104426379958955)
  ·
    refine ⟨6935597851656639569938433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4623731901104426379958955 6935597851656639569938433)
    ·
      refine ⟨5201698388742479677453825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6935597851656639569938433 5201698388742479677453825)
      ·
        refine ⟨3901273791556859758090369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5201698388742479677453825 3901273791556859758090369)
        ·
          refine ⟨2925955343667644818567777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3901273791556859758090369 2925955343667644818567777)
          ·
            refine ⟨2194466507750733613925833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2925955343667644818567777 2194466507750733613925833)
            ·
              refine ⟨1645849880813050210444375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2194466507750733613925833 1645849880813050210444375)
              ·
                refine ⟨2468774821219575315666563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645849880813050210444375 2468774821219575315666563)
                ·
                  refine ⟨3703162231829362973499845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468774821219575315666563 3703162231829362973499845)
                  ·
                    refine ⟨694342918468005557531221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3703162231829362973499845 694342918468005557531221)
                    ·
                      rfl

theorem cell22_2028342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_2028342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028342 prefixEnd_2028342 := by exact prefixLift 2028342
  have htrace : WordTrace (prefixWord ++ tailWord_2028342) baseStart_2028342 baseEnd_2028342 := by
    simpa [prefixWord, tailWord_2028342, baseEnd_2028342] using wordTrace_append hprefix tailTrace_2028342
  have hstable : (prefixWord ++ tailWord_2028342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028342).length < 2 ^ (prefixWord ++ tailWord_2028342).sum := by decide
  have hdescent : baseEnd_2028342 < baseStart_2028342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028471 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 2, 4]
def baseStart_2028471 : Nat := 118140960795 + 2028471 * 2 ^ 59
def prefixEnd_2028471 : Nat := 4983230072969 + 3 ^ 40 * 2028471 * 2
def baseEnd_2028471 : Nat := 694387077804292221055825

theorem tailTrace_2028471 : CollatzResearch.WordTrace tailWord_2028471 prefixEnd_2028471 694387077804292221055825 := by
  unfold tailWord_2028471
  simp only [CollatzResearch.WordTrace]
  refine ⟨73984415434203477110789267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49322943622802318073859511 73984415434203477110789267)
  ·
    refine ⟨110976623151305215666183901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73984415434203477110789267 110976623151305215666183901)
    ·
      refine ⟨41616233681739455874818963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110976623151305215666183901 41616233681739455874818963)
      ·
        refine ⟨62424350522609183812228445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41616233681739455874818963 62424350522609183812228445)
        ·
          refine ⟨23409131445978443929585667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62424350522609183812228445 23409131445978443929585667)
          ·
            refine ⟨35113697168967665894378501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23409131445978443929585667 35113697168967665894378501)
            ·
              refine ⟨6583818219181437355195969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35113697168967665894378501 6583818219181437355195969)
              ·
                refine ⟨4937863664386078016396977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6583818219181437355195969 4937863664386078016396977)
                ·
                  refine ⟨3703397748289558512297733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4937863664386078016396977 3703397748289558512297733)
                  ·
                    refine ⟨694387077804292221055825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3703397748289558512297733 694387077804292221055825)
                    ·
                      rfl

theorem cell22_2028471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_2028471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028471 prefixEnd_2028471 := by exact prefixLift 2028471
  have htrace : WordTrace (prefixWord ++ tailWord_2028471) baseStart_2028471 baseEnd_2028471 := by
    simpa [prefixWord, tailWord_2028471, baseEnd_2028471] using wordTrace_append hprefix tailTrace_2028471
  have hstable : (prefixWord ++ tailWord_2028471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028471).length < 2 ^ (prefixWord ++ tailWord_2028471).sum := by decide
  have hdescent : baseEnd_2028471 < baseStart_2028471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028473 : List Nat := [1, 2, 1, 4, 2, 2, 1, 4, 2, 3]
def baseStart_2028473 : Nat := 118140960795 + 2028473 * 2 ^ 59
def prefixEnd_2028473 : Nat := 4983230072969 + 3 ^ 40 * 2028473 * 2
def baseEnd_2028473 : Nat := 694387762445164882505819

theorem tailTrace_2028473 : CollatzResearch.WordTrace tailWord_2028473 prefixEnd_2028473 694387762445164882505819 := by
  unfold tailWord_2028473
  simp only [CollatzResearch.WordTrace]
  refine ⟨73984488380196231452362073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49322992253464154301574715 73984488380196231452362073)
  ·
    refine ⟨55488366285147173589271555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73984488380196231452362073 55488366285147173589271555)
    ·
      refine ⟨83232549427720760383907333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55488366285147173589271555 83232549427720760383907333)
      ·
        refine ⟨15606103017697642571982625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83232549427720760383907333 15606103017697642571982625)
        ·
          refine ⟨11704577263273231928986969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15606103017697642571982625 11704577263273231928986969)
          ·
            refine ⟨8778432947454923946740227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11704577263273231928986969 8778432947454923946740227)
            ·
              refine ⟨13167649421182385920110341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8778432947454923946740227 13167649421182385920110341)
              ·
                refine ⟨2468934266471697360020689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13167649421182385920110341 2468934266471697360020689)
                ·
                  refine ⟨1851700699853773020015517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2468934266471697360020689 1851700699853773020015517)
                  ·
                    refine ⟨694387762445164882505819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1851700699853773020015517 694387762445164882505819)
                    ·
                      rfl

theorem cell22_2028473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 3].length) (baseStart_2028473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028473 prefixEnd_2028473 := by exact prefixLift 2028473
  have htrace : WordTrace (prefixWord ++ tailWord_2028473) baseStart_2028473 baseEnd_2028473 := by
    simpa [prefixWord, tailWord_2028473, baseEnd_2028473] using wordTrace_append hprefix tailTrace_2028473
  have hstable : (prefixWord ++ tailWord_2028473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028473).length < 2 ^ (prefixWord ++ tailWord_2028473).sum := by decide
  have hdescent : baseEnd_2028473 < baseStart_2028473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028561 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 3, 4]
def baseStart_2028561 : Nat := 118140960795 + 2028561 * 2 ^ 59
def prefixEnd_2028561 : Nat := 4983230072969 + 3 ^ 40 * 2028561 * 2
def baseEnd_2028561 : Nat := 694417886643561986305549

theorem tailTrace_2028561 : CollatzResearch.WordTrace tailWord_2028561 prefixEnd_2028561 694417886643561986305549 := by
  unfold tailWord_2028561
  simp only [CollatzResearch.WordTrace]
  refine ⟨73987698003877422481565537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49325132002584948321043691 73987698003877422481565537)
  ·
    refine ⟨55490773502908066861174153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73987698003877422481565537 55490773502908066861174153)
    ·
      refine ⟨41618080127181050145880615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55490773502908066861174153 41618080127181050145880615)
      ·
        refine ⟨62427120190771575218820923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41618080127181050145880615 62427120190771575218820923)
        ·
          refine ⟨93640680286157362828231385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62427120190771575218820923 93640680286157362828231385)
          ·
            refine ⟨70230510214618022121173539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93640680286157362828231385 70230510214618022121173539)
            ·
              refine ⟨105345765321927033181760309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70230510214618022121173539 105345765321927033181760309)
              ·
                refine ⟨9876165498930659360790029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105345765321927033181760309 9876165498930659360790029)
                ·
                  refine ⟨3703562062098997260296261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9876165498930659360790029 3703562062098997260296261)
                  ·
                    refine ⟨694417886643561986305549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3703562062098997260296261 694417886643561986305549)
                    ·
                      rfl

theorem cell22_2028561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_2028561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028561 prefixEnd_2028561 := by exact prefixLift 2028561
  have htrace : WordTrace (prefixWord ++ tailWord_2028561) baseStart_2028561 baseEnd_2028561 := by
    simpa [prefixWord, tailWord_2028561, baseEnd_2028561] using wordTrace_append hprefix tailTrace_2028561
  have hstable : (prefixWord ++ tailWord_2028561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028561).length < 2 ^ (prefixWord ++ tailWord_2028561).sum := by decide
  have hdescent : baseEnd_2028561 < baseStart_2028561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028642 : List Nat := [3, 3, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_2028642 : Nat := 118140960795 + 2028642 * 2 ^ 59
def prefixEnd_2028642 : Nat := 4983230072969 + 3 ^ 40 * 2028642 * 2
def baseEnd_2028642 : Nat := 694445614598904775030301

theorem tailTrace_2028642 : CollatzResearch.WordTrace tailWord_2028642 prefixEnd_2028642 694445614598904775030301 := by
  unfold tailWord_2028642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18497663079145993328816045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49327101544389315543509453 18497663079145993328816045)
  ·
    refine ⟨6936623654679747498306017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18497663079145993328816045 6936623654679747498306017)
    ·
      refine ⟨5202467741009810623729513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6936623654679747498306017 5202467741009810623729513)
      ·
        refine ⟨3901850805757357967797135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5202467741009810623729513 3901850805757357967797135)
        ·
          refine ⟨5852776208636036951695703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3901850805757357967797135 5852776208636036951695703)
          ·
            refine ⟨8779164312954055427543555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5852776208636036951695703 8779164312954055427543555)
            ·
              refine ⟨13168746469431083141315333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8779164312954055427543555 13168746469431083141315333)
              ·
                refine ⟨2469139963018328088996625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13168746469431083141315333 2469139963018328088996625)
                ·
                  refine ⟨1851854972263746066747469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2469139963018328088996625 1851854972263746066747469)
                  ·
                    refine ⟨694445614598904775030301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1851854972263746066747469 694445614598904775030301)
                    ·
                      rfl

theorem cell22_2028642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_2028642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028642 prefixEnd_2028642 := by exact prefixLift 2028642
  have htrace : WordTrace (prefixWord ++ tailWord_2028642) baseStart_2028642 baseEnd_2028642 := by
    simpa [prefixWord, tailWord_2028642, baseEnd_2028642] using wordTrace_append hprefix tailTrace_2028642
  have hstable : (prefixWord ++ tailWord_2028642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028642).length < 2 ^ (prefixWord ++ tailWord_2028642).sum := by decide
  have hdescent : baseEnd_2028642 < baseStart_2028642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028700 : List Nat := [2, 2, 3, 2, 1, 2, 3, 2, 5]
def baseStart_2028700 : Nat := 118140960795 + 2028700 * 2 ^ 59
def prefixEnd_2028700 : Nat := 4983230072969 + 3 ^ 40 * 2028700 * 2
def baseEnd_2028700 : Nat := 231488489728070652360041

theorem tailTrace_2028700 : CollatzResearch.WordTrace tailWord_2028700 prefixEnd_2028700 231488489728070652360041 := by
  unfold tailWord_2028700
  simp only [CollatzResearch.WordTrace]
  refine ⟨36996383875186924610437777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49328511833582566147250369 36996383875186924610437777)
  ·
    refine ⟨27747287906390193457828333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36996383875186924610437777 27747287906390193457828333)
    ·
      refine ⟨10405232964896322546685625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27747287906390193457828333 10405232964896322546685625)
      ·
        refine ⟨7803924723672241910014219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10405232964896322546685625 7803924723672241910014219)
        ·
          refine ⟨11705887085508362865021329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7803924723672241910014219 11705887085508362865021329)
          ·
            refine ⟨8779415314131272148765997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11705887085508362865021329 8779415314131272148765997)
            ·
              refine ⟨3292280742799227055787249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8779415314131272148765997 3292280742799227055787249)
              ·
                refine ⟨2469210557099420291840437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3292280742799227055787249 2469210557099420291840437)
                ·
                  refine ⟨231488489728070652360041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2469210557099420291840437 231488489728070652360041)
                  ·
                    rfl

theorem cell22_2028700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_2028700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028700 prefixEnd_2028700 := by exact prefixLift 2028700
  have htrace : WordTrace (prefixWord ++ tailWord_2028700) baseStart_2028700 baseEnd_2028700 := by
    simpa [prefixWord, tailWord_2028700, baseEnd_2028700] using wordTrace_append hprefix tailTrace_2028700
  have hstable : (prefixWord ++ tailWord_2028700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028700).length < 2 ^ (prefixWord ++ tailWord_2028700).sum := by decide
  have hdescent : baseEnd_2028700 < baseStart_2028700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028743 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 1, 5]
def baseStart_2028743 : Nat := 118140960795 + 2028743 * 2 ^ 59
def prefixEnd_2028743 : Nat := 4983230072969 + 3 ^ 40 * 2028743 * 2
def baseEnd_2028743 : Nat := 694480188962974178254991

theorem tailTrace_2028743 : CollatzResearch.WordTrace tailWord_2028743 prefixEnd_2028743 694480188962974178254991 := by
  unfold tailWord_2028743
  simp only [CollatzResearch.WordTrace]
  refine ⟨73994336089218067564690883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49329557392812045043127255 73994336089218067564690883)
  ·
    refine ⟨110991504133827101347036325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73994336089218067564690883 110991504133827101347036325)
    ·
      refine ⟨20810907025092581502569311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110991504133827101347036325 20810907025092581502569311)
      ·
        refine ⟨31216360537638872253853967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20810907025092581502569311 31216360537638872253853967)
        ·
          refine ⟨46824540806458308380780951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31216360537638872253853967 46824540806458308380780951)
          ·
            refine ⟨70236811209687462571171427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46824540806458308380780951 70236811209687462571171427)
            ·
              refine ⟨105355216814531193856757141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70236811209687462571171427 105355216814531193856757141)
              ·
                refine ⟨4938525788181149712035491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105355216814531193856757141 4938525788181149712035491)
                ·
                  refine ⟨7407788682271724568053237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4938525788181149712035491 7407788682271724568053237)
                  ·
                    refine ⟨694480188962974178254991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7407788682271724568053237 694480188962974178254991)
                    ·
                      rfl

theorem cell22_2028743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_2028743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028743 prefixEnd_2028743 := by exact prefixLift 2028743
  have htrace : WordTrace (prefixWord ++ tailWord_2028743) baseStart_2028743 baseEnd_2028743 := by
    simpa [prefixWord, tailWord_2028743, baseEnd_2028743] using wordTrace_append hprefix tailTrace_2028743
  have hstable : (prefixWord ++ tailWord_2028743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028743).length < 2 ^ (prefixWord ++ tailWord_2028743).sum := by decide
  have hdescent : baseEnd_2028743 < baseStart_2028743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028835 : List Nat := [1, 1, 1, 4, 2, 3, 2, 3, 5]
def baseStart_2028835 : Nat := 118140960795 + 2028835 * 2 ^ 59
def prefixEnd_2028835 : Nat := 4983230072969 + 3 ^ 40 * 2028835 * 2
def baseEnd_2028835 : Nat := 231503894147705534984903

theorem tailTrace_2028835 : CollatzResearch.WordTrace tailWord_2028835 prefixEnd_2028835 231503894147705534984903 := by
  unfold tailWord_2028835
  simp only [CollatzResearch.WordTrace]
  refine ⟨73997691604884767277039959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49331794403256511518026639 73997691604884767277039959)
  ·
    refine ⟨110996537407327150915559939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73997691604884767277039959 110996537407327150915559939)
    ·
      refine ⟨166494806110990726373339909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110996537407327150915559939 166494806110990726373339909)
      ·
        refine ⟨31217776145810761195001233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166494806110990726373339909 31217776145810761195001233)
        ·
          refine ⟨23413332109358070896250925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31217776145810761195001233 23413332109358070896250925)
          ·
            refine ⟨8779999541009276586094097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23413332109358070896250925 8779999541009276586094097)
            ·
              refine ⟨6584999655756957439570573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8779999541009276586094097 6584999655756957439570573)
              ·
                refine ⟨2469374870908859039838965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6584999655756957439570573 2469374870908859039838965)
                ·
                  refine ⟨231503894147705534984903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2469374870908859039838965 231503894147705534984903)
                  ·
                    rfl

theorem cell22_2028835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 5].length) (baseStart_2028835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028835 prefixEnd_2028835 := by exact prefixLift 2028835
  have htrace : WordTrace (prefixWord ++ tailWord_2028835) baseStart_2028835 baseEnd_2028835 := by
    simpa [prefixWord, tailWord_2028835, baseEnd_2028835] using wordTrace_append hprefix tailTrace_2028835
  have hstable : (prefixWord ++ tailWord_2028835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028835).length < 2 ^ (prefixWord ++ tailWord_2028835).sum := by decide
  have hdescent : baseEnd_2028835 < baseStart_2028835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028880 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 6]
def baseStart_2028880 : Nat := 118140960795 + 2028880 * 2 ^ 59
def prefixEnd_2028880 : Nat := 4983230072969 + 3 ^ 40 * 2028880 * 2
def baseEnd_2028880 : Nat := 231509028954250495859857

theorem tailTrace_2028880 : CollatzResearch.WordTrace tailWord_2028880 prefixEnd_2028880 231509028954250495859857 := by
  unfold tailWord_2028880
  simp only [CollatzResearch.WordTrace]
  refine ⟨36999666444860869981214047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49332888593147826641618729 36999666444860869981214047)
  ·
    refine ⟨55499499667291304971821071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36999666444860869981214047 55499499667291304971821071)
    ·
      refine ⟨83249249500936957457731607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55499499667291304971821071 83249249500936957457731607)
      ·
        refine ⟨124873874251405436186597411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83249249500936957457731607 124873874251405436186597411)
        ·
          refine ⟨187310811377108154279896117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124873874251405436186597411 187310811377108154279896117)
          ·
            refine ⟨17560388566603889463740261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187310811377108154279896117 17560388566603889463740261)
            ·
              refine ⟨3292572856238229274451299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17560388566603889463740261 3292572856238229274451299)
              ·
                refine ⟨4938859284357343911676949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3292572856238229274451299 4938859284357343911676949)
                ·
                  refine ⟨231509028954250495859857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4938859284357343911676949 231509028954250495859857)
                  ·
                    rfl

theorem cell22_2028880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 6].length) (baseStart_2028880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2028880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2028880 prefixEnd_2028880 := by exact prefixLift 2028880
  have htrace : WordTrace (prefixWord ++ tailWord_2028880) baseStart_2028880 baseEnd_2028880 := by
    simpa [prefixWord, tailWord_2028880, baseEnd_2028880] using wordTrace_append hprefix tailTrace_2028880
  have hstable : (prefixWord ++ tailWord_2028880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028880).length < 2 ^ (prefixWord ++ tailWord_2028880).sum := by decide
  have hdescent : baseEnd_2028880 < baseStart_2028880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029002 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_2029002 : Nat := 118140960795 + 2029002 * 2 ^ 59
def prefixEnd_2029002 : Nat := 4983230072969 + 3 ^ 40 * 2029002 * 2
def baseEnd_2029002 : Nat := 694568849955983836029197

theorem tailTrace_2029002 : CollatzResearch.WordTrace tailWord_2029002 prefixEnd_2029002 694568849955983836029197 := by
  unfold tailWord_2029002
  simp only [CollatzResearch.WordTrace]
  refine ⟨18500945648819938699592315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49335855063519836532246173 18500945648819938699592315)
  ·
    refine ⟨27751418473229908049388473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18500945648819938699592315 27751418473229908049388473)
    ·
      refine ⟨20813563854922431037041355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27751418473229908049388473 20813563854922431037041355)
      ·
        refine ⟨31220345782383646555562033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20813563854922431037041355 31220345782383646555562033)
        ·
          refine ⟨23415259336787734916671525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31220345782383646555562033 23415259336787734916671525)
          ·
            refine ⟨4390361125647700296875911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23415259336787734916671525 4390361125647700296875911)
            ·
              refine ⟨6585541688471550445313867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390361125647700296875911 6585541688471550445313867)
              ·
                refine ⟨9878312532707325667970801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6585541688471550445313867 9878312532707325667970801)
                ·
                  refine ⟨7408734399530494250978101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9878312532707325667970801 7408734399530494250978101)
                  ·
                    refine ⟨694568849955983836029197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7408734399530494250978101 694568849955983836029197)
                    ·
                      rfl

theorem cell22_2029002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_2029002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029002 prefixEnd_2029002 := by exact prefixLift 2029002
  have htrace : WordTrace (prefixWord ++ tailWord_2029002) baseStart_2029002 baseEnd_2029002 := by
    simpa [prefixWord, tailWord_2029002, baseEnd_2029002] using wordTrace_append hprefix tailTrace_2029002
  have hstable : (prefixWord ++ tailWord_2029002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029002).length < 2 ^ (prefixWord ++ tailWord_2029002).sum := by decide
  have hdescent : baseEnd_2029002 < baseStart_2029002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029017 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 3, 4]
def baseStart_2029017 : Nat := 118140960795 + 2029017 * 2 ^ 59
def prefixEnd_2029017 : Nat := 4983230072969 + 3 ^ 40 * 2029017 * 2
def baseEnd_2029017 : Nat := 694573984762528796904151

theorem tailTrace_2029017 : CollatzResearch.WordTrace tailWord_2029017 prefixEnd_2029017 694573984762528796904151 := by
  unfold tailWord_2029017
  simp only [CollatzResearch.WordTrace]
  refine ⟨74004329690225412360165305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49336219793483608240110203 74004329690225412360165305)
  ·
    refine ⟨55503247267669059270123979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74004329690225412360165305 55503247267669059270123979)
    ·
      refine ⟨83254870901503588905185969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55503247267669059270123979 83254870901503588905185969)
      ·
        refine ⟨62441153176127691678889477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83254870901503588905185969 62441153176127691678889477)
        ·
          refine ⟨11707716220523942189791777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62441153176127691678889477 11707716220523942189791777)
          ·
            refine ⟨8780787165392956642343833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11707716220523942189791777 8780787165392956642343833)
            ·
              refine ⟨6585590374044717481757875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8780787165392956642343833 6585590374044717481757875)
              ·
                refine ⟨9878385561067076222636813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6585590374044717481757875 9878385561067076222636813)
                ·
                  refine ⟨3704394585400153583488805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9878385561067076222636813 3704394585400153583488805)
                  ·
                    refine ⟨694573984762528796904151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3704394585400153583488805 694573984762528796904151)
                    ·
                      rfl

theorem cell22_2029017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_2029017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029017 prefixEnd_2029017 := by exact prefixLift 2029017
  have htrace : WordTrace (prefixWord ++ tailWord_2029017) baseStart_2029017 baseEnd_2029017 := by
    simpa [prefixWord, tailWord_2029017, baseEnd_2029017] using wordTrace_append hprefix tailTrace_2029017
  have hstable : (prefixWord ++ tailWord_2029017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029017).length < 2 ^ (prefixWord ++ tailWord_2029017).sum := by decide
  have hdescent : baseEnd_2029017 < baseStart_2029017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029064 : List Nat := [2, 1, 3, 2, 1, 1, 2, 5, 2, 3]
def baseStart_2029064 : Nat := 118140960795 + 2029064 * 2 ^ 59
def prefixEnd_2029064 : Nat := 4983230072969 + 3 ^ 40 * 2029064 * 2
def baseEnd_2029064 : Nat := 694590073823036340979007

theorem tailTrace_2029064 : CollatzResearch.WordTrace tailWord_2029064 prefixEnd_2029064 694590073823036340979007 := by
  unfold tailWord_2029064
  simp only [CollatzResearch.WordTrace]
  refine ⟨37003021960527569693563123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49337362614036759591417497 37003021960527569693563123)
  ·
    refine ⟨55504532940791354540344685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37003021960527569693563123 55504532940791354540344685)
    ·
      refine ⟨20814199852796757952629257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55504532940791354540344685 20814199852796757952629257)
      ·
        refine ⟨15610649889597568464471943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20814199852796757952629257 15610649889597568464471943)
        ·
          refine ⟨23415974834396352696707915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15610649889597568464471943 23415974834396352696707915)
          ·
            refine ⟨35123962251594529045061873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23415974834396352696707915 35123962251594529045061873)
            ·
              refine ⟨26342971688695896783796405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35123962251594529045061873 26342971688695896783796405)
              ·
                refine ⟨2469653595815240323480913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26342971688695896783796405 2469653595815240323480913)
                ·
                  refine ⟨1852240196861430242610685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2469653595815240323480913 1852240196861430242610685)
                  ·
                    refine ⟨694590073823036340979007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1852240196861430242610685 694590073823036340979007)
                    ·
                      rfl

theorem cell22_2029064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_2029064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029064 prefixEnd_2029064 := by exact prefixLift 2029064
  have htrace : WordTrace (prefixWord ++ tailWord_2029064) baseStart_2029064 baseEnd_2029064 := by
    simpa [prefixWord, tailWord_2029064, baseEnd_2029064] using wordTrace_append hprefix tailTrace_2029064
  have hstable : (prefixWord ++ tailWord_2029064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029064).length < 2 ^ (prefixWord ++ tailWord_2029064).sum := by decide
  have hdescent : baseEnd_2029064 < baseStart_2029064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029077 : List Nat := [1, 3, 2, 1, 3, 3, 1, 8]
def baseStart_2029077 : Nat := 118140960795 + 2029077 * 2 ^ 59
def prefixEnd_2029077 : Nat := 4983230072969 + 3 ^ 40 * 2029077 * 2
def baseEnd_2029077 : Nat := 77177169332078737822663

theorem tailTrace_2029077 : CollatzResearch.WordTrace tailWord_2029077 prefixEnd_2029077 77177169332078737822663 := by
  unfold tailWord_2029077
  simp only [CollatzResearch.WordTrace]
  refine ⟨74006518070008042607349485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49337678713338695071566323 74006518070008042607349485)
  ·
    refine ⟨27752444276253015977756057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74006518070008042607349485 27752444276253015977756057)
    ·
      refine ⟨20814333207189761983317043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27752444276253015977756057 20814333207189761983317043)
      ·
        refine ⟨31221499810784642974975565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20814333207189761983317043 31221499810784642974975565)
        ·
          refine ⟨11708062429044241115615837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31221499810784642974975565 11708062429044241115615837)
          ·
            refine ⟨4390523410891590418355939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11708062429044241115615837 4390523410891590418355939)
            ·
              refine ⟨6585785116337385627533909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390523410891590418355939 6585785116337385627533909)
              ·
                refine ⟨77177169332078737822663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6585785116337385627533909 77177169332078737822663)
                ·
                  rfl

theorem cell22_2029077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 8].length) (baseStart_2029077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029077 prefixEnd_2029077 := by exact prefixLift 2029077
  have htrace : WordTrace (prefixWord ++ tailWord_2029077) baseStart_2029077 baseEnd_2029077 := by
    simpa [prefixWord, tailWord_2029077, baseEnd_2029077] using wordTrace_append hprefix tailTrace_2029077
  have hstable : (prefixWord ++ tailWord_2029077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029077).length < 2 ^ (prefixWord ++ tailWord_2029077).sum := by decide
  have hdescent : baseEnd_2029077 < baseStart_2029077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029096 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 2, 4]
def baseStart_2029096 : Nat := 118140960795 + 2029096 * 2 ^ 59
def prefixEnd_2029096 : Nat := 4983230072969 + 3 ^ 40 * 2029096 * 2
def baseEnd_2029096 : Nat := 694601028076998924178909

theorem tailTrace_2029096 : CollatzResearch.WordTrace tailWord_2029096 prefixEnd_2029096 694601028076998924178909 := by
  unfold tailWord_2029096
  simp only [CollatzResearch.WordTrace]
  refine ⟨37003605528469604426145571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49338140704626139234860761 37003605528469604426145571)
  ·
    refine ⟨55505408292704406639218357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37003605528469604426145571 55505408292704406639218357)
    ·
      refine ⟨5203632027441038122426721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55505408292704406639218357 5203632027441038122426721)
      ·
        refine ⟨3902724020580778591820041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5203632027441038122426721 3902724020580778591820041)
        ·
          refine ⟨2927043015435583943865031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3902724020580778591820041 2927043015435583943865031)
          ·
            refine ⟨4390564523153375915797547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927043015435583943865031 4390564523153375915797547)
            ·
              refine ⟨6585846784730063873696321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390564523153375915797547 6585846784730063873696321)
              ·
                refine ⟨4939385088547547905272241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6585846784730063873696321 4939385088547547905272241)
                ·
                  refine ⟨3704538816410660928954181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4939385088547547905272241 3704538816410660928954181)
                  ·
                    refine ⟨694601028076998924178909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3704538816410660928954181 694601028076998924178909)
                    ·
                      rfl

theorem cell22_2029096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_2029096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029096 prefixEnd_2029096 := by exact prefixLift 2029096
  have htrace : WordTrace (prefixWord ++ tailWord_2029096) baseStart_2029096 baseEnd_2029096 := by
    simpa [prefixWord, tailWord_2029096, baseEnd_2029096] using wordTrace_append hprefix tailTrace_2029096
  have hstable : (prefixWord ++ tailWord_2029096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029096).length < 2 ^ (prefixWord ++ tailWord_2029096).sum := by decide
  have hdescent : baseEnd_2029096 < baseStart_2029096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029160 : List Nat := [2, 1, 4, 3, 1, 1, 4, 2, 1, 3]
def baseStart_2029160 : Nat := 118140960795 + 2029160 * 2 ^ 59
def prefixEnd_2029160 : Nat := 4983230072969 + 3 ^ 40 * 2029160 * 2
def baseEnd_2029160 : Nat := 694622936584924090578713

theorem tailTrace_2029160 : CollatzResearch.WordTrace tailWord_2029160 prefixEnd_2029160 694622936584924090578713 := by
  unfold tailWord_2029160
  simp only [CollatzResearch.WordTrace]
  refine ⟨37004772664353673891310467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49339696885804898521747289 37004772664353673891310467)
  ·
    refine ⟨55507158996530510836965701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37004772664353673891310467 55507158996530510836965701)
    ·
      refine ⟨10407592311849470781931069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55507158996530510836965701 10407592311849470781931069)
      ·
        refine ⟨3902847116943551543224151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10407592311849470781931069 3902847116943551543224151)
        ·
          refine ⟨5854270675415327314836227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3902847116943551543224151 5854270675415327314836227)
          ·
            refine ⟨8781406013122990972254341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5854270675415327314836227 8781406013122990972254341)
            ·
              refine ⟨1646513627460560807297689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8781406013122990972254341 1646513627460560807297689)
              ·
                refine ⟨1234885220595420605473267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1646513627460560807297689 1234885220595420605473267)
                ·
                  refine ⟨1852327830893130908209901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1234885220595420605473267 1852327830893130908209901)
                  ·
                    refine ⟨694622936584924090578713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1852327830893130908209901 694622936584924090578713)
                    ·
                      rfl

theorem cell22_2029160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_2029160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029160 prefixEnd_2029160 := by exact prefixLift 2029160
  have htrace : WordTrace (prefixWord ++ tailWord_2029160) baseStart_2029160 baseEnd_2029160 := by
    simpa [prefixWord, tailWord_2029160, baseEnd_2029160] using wordTrace_append hprefix tailTrace_2029160
  have hstable : (prefixWord ++ tailWord_2029160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029160).length < 2 ^ (prefixWord ++ tailWord_2029160).sum := by decide
  have hdescent : baseEnd_2029160 < baseStart_2029160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029167 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 6]
def baseStart_2029167 : Nat := 118140960795 + 2029167 * 2 ^ 59
def prefixEnd_2029167 : Nat := 4983230072969 + 3 ^ 40 * 2029167 * 2
def baseEnd_2029167 : Nat := 231541777609326135217897

theorem tailTrace_2029167 : CollatzResearch.WordTrace tailWord_2029167 prefixEnd_2029167 231541777609326135217897 := by
  unfold tailWord_2029167
  simp only [CollatzResearch.WordTrace]
  refine ⟨74009800639681987978125755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49339867093121325318750503 74009800639681987978125755)
  ·
    refine ⟨111014700959522981967188633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74009800639681987978125755 111014700959522981967188633)
    ·
      refine ⟨83261025719642236475391475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111014700959522981967188633 83261025719642236475391475)
      ·
        refine ⟨124891538579463354713087213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83261025719642236475391475 124891538579463354713087213)
        ·
          refine ⟨46834326967298758017407705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124891538579463354713087213 46834326967298758017407705)
          ·
            refine ⟨35125745225474068513055779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46834326967298758017407705 35125745225474068513055779)
            ·
              refine ⟨52688617838211102769583669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35125745225474068513055779 52688617838211102769583669)
              ·
                refine ⟨4939557922332290884648469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52688617838211102769583669 4939557922332290884648469)
                ·
                  refine ⟨231541777609326135217897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4939557922332290884648469 231541777609326135217897)
                  ·
                    rfl

theorem cell22_2029167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 6].length) (baseStart_2029167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029167 prefixEnd_2029167 := by exact prefixLift 2029167
  have htrace : WordTrace (prefixWord ++ tailWord_2029167) baseStart_2029167 baseEnd_2029167 := by
    simpa [prefixWord, tailWord_2029167, baseEnd_2029167] using wordTrace_append hprefix tailTrace_2029167
  have hstable : (prefixWord ++ tailWord_2029167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029167).length < 2 ^ (prefixWord ++ tailWord_2029167).sum := by decide
  have hdescent : baseEnd_2029167 < baseStart_2029167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029216 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 4, 3]
def baseStart_2029216 : Nat := 118140960795 + 2029216 * 2 ^ 59
def prefixEnd_2029216 : Nat := 4983230072969 + 3 ^ 40 * 2029216 * 2
def baseEnd_2029216 : Nat := 694642106529358611178541

theorem tailTrace_2029216 : CollatzResearch.WordTrace tailWord_2029216 prefixEnd_2029216 694642106529358611178541 := by
  unfold tailWord_2029216
  simp only [CollatzResearch.WordTrace]
  refine ⟨37005793908252234673329751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49341058544336312897773001 37005793908252234673329751)
  ·
    refine ⟨55508690862378352009994627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37005793908252234673329751 55508690862378352009994627)
    ·
      refine ⟨83263036293567528014991941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55508690862378352009994627 83263036293567528014991941)
      ·
        refine ⟨15611819305043911502810989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83263036293567528014991941 15611819305043911502810989)
        ·
          refine ⟨5854432239391466813554121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15611819305043911502810989 5854432239391466813554121)
          ·
            refine ⟨4390824179543600110165591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5854432239391466813554121 4390824179543600110165591)
            ·
              refine ⟨6586236269315400165248387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390824179543600110165591 6586236269315400165248387)
              ·
                refine ⟨9879354403973100247872581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6586236269315400165248387 9879354403973100247872581)
                ·
                  refine ⟨1852378950744956296476109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9879354403973100247872581 1852378950744956296476109)
                  ·
                    refine ⟨694642106529358611178541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1852378950744956296476109 694642106529358611178541)
                    ·
                      rfl

theorem cell22_2029216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 4, 3].length) (baseStart_2029216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029216 prefixEnd_2029216 := by exact prefixLift 2029216
  have htrace : WordTrace (prefixWord ++ tailWord_2029216) baseStart_2029216 baseEnd_2029216 := by
    simpa [prefixWord, tailWord_2029216, baseEnd_2029216] using wordTrace_append hprefix tailTrace_2029216
  have hstable : (prefixWord ++ tailWord_2029216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029216).length < 2 ^ (prefixWord ++ tailWord_2029216).sum := by decide
  have hdescent : baseEnd_2029216 < baseStart_2029216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029218 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 6]
def baseStart_2029218 : Nat := 118140960795 + 2029218 * 2 ^ 59
def prefixEnd_2029218 : Nat := 4983230072969 + 3 ^ 40 * 2029218 * 2
def baseEnd_2029218 : Nat := 231547597056743757542845

theorem tailTrace_2029218 : CollatzResearch.WordTrace tailWord_2029218 prefixEnd_2029218 231547597056743757542845 := by
  unfold tailWord_2029218
  simp only [CollatzResearch.WordTrace]
  refine ⟨18502915190624305922058077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49341107174998149125488205 18502915190624305922058077)
  ·
    refine ⟨6938593196484114720771779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18502915190624305922058077 6938593196484114720771779)
    ·
      refine ⟨10407889794726172081157669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6938593196484114720771779 10407889794726172081157669)
      ·
        refine ⟨1951479336511157265217063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10407889794726172081157669 1951479336511157265217063)
        ·
          refine ⟨2927219004766735897825595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1951479336511157265217063 2927219004766735897825595)
          ·
            refine ⟨4390828507150103846738393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927219004766735897825595 4390828507150103846738393)
            ·
              refine ⟨3293121380362577885053795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4390828507150103846738393 3293121380362577885053795)
              ·
                refine ⟨4939682070543866827580693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3293121380362577885053795 4939682070543866827580693)
                ·
                  refine ⟨231547597056743757542845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4939682070543866827580693 231547597056743757542845)
                  ·
                    rfl

theorem cell22_2029218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_2029218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029218 prefixEnd_2029218 := by exact prefixLift 2029218
  have htrace : WordTrace (prefixWord ++ tailWord_2029218) baseStart_2029218 baseEnd_2029218 := by
    simpa [prefixWord, tailWord_2029218, baseEnd_2029218] using wordTrace_append hprefix tailTrace_2029218
  have hstable : (prefixWord ++ tailWord_2029218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029218).length < 2 ^ (prefixWord ++ tailWord_2029218).sum := by decide
  have hdescent : baseEnd_2029218 < baseStart_2029218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029229 : List Nat := [1, 5, 2, 1, 1, 1, 2, 9]
def baseStart_2029229 : Nat := 118140960795 + 2029229 * 2 ^ 59
def prefixEnd_2029229 : Nat := 4983230072969 + 3 ^ 40 * 2029229 * 2
def baseEnd_2029229 : Nat := 77182950743892323400389

theorem tailTrace_2029229 : CollatzResearch.WordTrace tailWord_2029229 prefixEnd_2029229 77182950743892323400389 := by
  unfold tailWord_2029229
  simp only [CollatzResearch.WordTrace]
  refine ⟨74012061965457372566882741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49341374643638248377921827 74012061965457372566882741)
  ·
    refine ⟨6938630809261628678145257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74012061965457372566882741 6938630809261628678145257)
    ·
      refine ⟨5203973106946221508608943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6938630809261628678145257 5203973106946221508608943)
      ·
        refine ⟨7805959660419332262913415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5203973106946221508608943 7805959660419332262913415)
        ·
          refine ⟨11708939490628998394370123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7805959660419332262913415 11708939490628998394370123)
          ·
            refine ⟨17563409235943497591555185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11708939490628998394370123 17563409235943497591555185)
            ·
              refine ⟨13172556926957623193666389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17563409235943497591555185 13172556926957623193666389)
              ·
                refine ⟨77182950743892323400389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13172556926957623193666389 77182950743892323400389)
                ·
                  rfl

theorem cell22_2029229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 9].length) (baseStart_2029229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029229 prefixEnd_2029229 := by exact prefixLift 2029229
  have htrace : WordTrace (prefixWord ++ tailWord_2029229) baseStart_2029229 baseEnd_2029229 := by
    simpa [prefixWord, tailWord_2029229, baseEnd_2029229] using wordTrace_append hprefix tailTrace_2029229
  have hstable : (prefixWord ++ tailWord_2029229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029229).length < 2 ^ (prefixWord ++ tailWord_2029229).sum := by decide
  have hdescent : baseEnd_2029229 < baseStart_2029229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029246 : List Nat := [4, 2, 1, 1, 2, 2, 4, 6]
def baseStart_2029246 : Nat := 118140960795 + 2029246 * 2 ^ 59
def prefixEnd_2029246 : Nat := 4983230072969 + 3 ^ 40 * 2029246 * 2
def baseEnd_2029246 : Nat := 77183597349160948103161

theorem tailTrace_2029246 : CollatzResearch.WordTrace tailWord_2029246 prefixEnd_2029246 77183597349160948103161 := by
  unfold tailWord_2029246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9251585250799473058781449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49341788004263856313501061 9251585250799473058781449)
  ·
    refine ⟨6938688938099604794086087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9251585250799473058781449 6938688938099604794086087)
    ·
      refine ⟨10408033407149407191129131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6938688938099604794086087 10408033407149407191129131)
      ·
        refine ⟨15612050110724110786693697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10408033407149407191129131 15612050110724110786693697)
        ·
          refine ⟨11709037583043083090020273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15612050110724110786693697 11709037583043083090020273)
          ·
            refine ⟨8781778187282312317515205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11709037583043083090020273 8781778187282312317515205)
            ·
              refine ⟨1646583410115433559534101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8781778187282312317515205 1646583410115433559534101)
              ·
                refine ⟨77183597349160948103161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1646583410115433559534101 77183597349160948103161)
                ·
                  rfl

theorem cell22_2029246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_2029246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029246 prefixEnd_2029246 := by exact prefixLift 2029246
  have htrace : WordTrace (prefixWord ++ tailWord_2029246) baseStart_2029246 baseEnd_2029246 := by
    simpa [prefixWord, tailWord_2029246, baseEnd_2029246] using wordTrace_append hprefix tailTrace_2029246
  have hstable : (prefixWord ++ tailWord_2029246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029246).length < 2 ^ (prefixWord ++ tailWord_2029246).sum := by decide
  have hdescent : baseEnd_2029246 < baseStart_2029246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029274 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 7]
def baseStart_2029274 : Nat := 118140960795 + 2029274 * 2 ^ 59
def prefixEnd_2029274 : Nat := 4983230072969 + 3 ^ 40 * 2029274 * 2
def baseEnd_2029274 : Nat := 231553987038221931076121

theorem tailTrace_2029274 : CollatzResearch.WordTrace tailWord_2029274 prefixEnd_2029274 231553987038221931076121 := by
  unfold tailWord_2029274
  simp only [CollatzResearch.WordTrace]
  refine ⟨18503425812573586313067719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49342468833529563501513917 18503425812573586313067719)
  ·
    refine ⟨27755138718860379469601579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18503425812573586313067719 27755138718860379469601579)
    ·
      refine ⟨41632708078290569204402369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27755138718860379469601579 41632708078290569204402369)
      ·
        refine ⟨31224531058717926903301777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41632708078290569204402369 31224531058717926903301777)
        ·
          refine ⟨23418398294038445177476333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31224531058717926903301777 23418398294038445177476333)
          ·
            refine ⟨8781899360264416941553625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23418398294038445177476333 8781899360264416941553625)
            ·
              refine ⟨6586424520198312706165219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8781899360264416941553625 6586424520198312706165219)
              ·
                refine ⟨9879636780297469059247829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6586424520198312706165219 9879636780297469059247829)
                ·
                  refine ⟨231553987038221931076121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9879636780297469059247829 231553987038221931076121)
                  ·
                    rfl

theorem cell22_2029274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_2029274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029274 prefixEnd_2029274 := by exact prefixLift 2029274
  have htrace : WordTrace (prefixWord ++ tailWord_2029274) baseStart_2029274 baseEnd_2029274 := by
    simpa [prefixWord, tailWord_2029274, baseEnd_2029274] using wordTrace_append hprefix tailTrace_2029274
  have hstable : (prefixWord ++ tailWord_2029274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029274).length < 2 ^ (prefixWord ++ tailWord_2029274).sum := by decide
  have hdescent : baseEnd_2029274 < baseStart_2029274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029291 : List Nat := [1, 1, 1, 1, 2, 4, 6, 1, 5]
def baseStart_2029291 : Nat := 118140960795 + 2029291 * 2 ^ 59
def prefixEnd_2029291 : Nat := 4983230072969 + 3 ^ 40 * 2029291 * 2
def baseEnd_2029291 : Nat := 231555926854027805184437

theorem tailTrace_2029291 : CollatzResearch.WordTrace tailWord_2029291 prefixEnd_2029291 231555926854027805184437 := by
  unfold tailWord_2029291
  simp only [CollatzResearch.WordTrace]
  refine ⟨74014323291232757155639727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49342882194155171437093151 74014323291232757155639727)
  ·
    refine ⟨111021484936849135733459591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74014323291232757155639727 111021484936849135733459591)
    ·
      refine ⟨166532227405273703600189387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111021484936849135733459591 166532227405273703600189387)
      ·
        refine ⟨249798341107910555400284081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166532227405273703600189387 249798341107910555400284081)
        ·
          refine ⟨187348755830932916550213061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249798341107910555400284081 187348755830932916550213061)
          ·
            refine ⟨35127891718299921853164949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187348755830932916550213061 35127891718299921853164949)
            ·
              refine ⟨1646619924295308836867107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35127891718299921853164949 1646619924295308836867107)
              ·
                refine ⟨2469929886442963255300661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646619924295308836867107 2469929886442963255300661)
                ·
                  refine ⟨231555926854027805184437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2469929886442963255300661 231555926854027805184437)
                  ·
                    rfl

theorem cell22_2029291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 5].length) (baseStart_2029291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029291 prefixEnd_2029291 := by exact prefixLift 2029291
  have htrace : WordTrace (prefixWord ++ tailWord_2029291) baseStart_2029291 baseEnd_2029291 := by
    simpa [prefixWord, tailWord_2029291, baseEnd_2029291] using wordTrace_append hprefix tailTrace_2029291
  have hstable : (prefixWord ++ tailWord_2029291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029291).length < 2 ^ (prefixWord ++ tailWord_2029291).sum := by decide
  have hdescent : baseEnd_2029291 < baseStart_2029291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029447 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 3, 3]
def baseStart_2029447 : Nat := 118140960795 + 2029447 * 2 ^ 59
def prefixEnd_2029447 : Nat := 4983230072969 + 3 ^ 40 * 2029447 * 2
def baseEnd_2029447 : Nat := 694721182550151008652833

theorem tailTrace_2029447 : CollatzResearch.WordTrace tailWord_2029447 prefixEnd_2029447 694721182550151008652833 := by
  unfold tailWord_2029447
  simp only [CollatzResearch.WordTrace]
  refine ⟨74020013078667595798318595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49346675385778397198879063 74020013078667595798318595)
  ·
    refine ⟨111030019618001393697477893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74020013078667595798318595 111030019618001393697477893)
    ·
      refine ⟨20818128678375261318277105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111030019618001393697477893 20818128678375261318277105)
      ·
        refine ⟨15613596508781445988707829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20818128678375261318277105 15613596508781445988707829)
        ·
          refine ⟨1463774672698260561441359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15613596508781445988707829 1463774672698260561441359)
          ·
            refine ⟨2195662009047390842162039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463774672698260561441359 2195662009047390842162039)
            ·
              refine ⟨3293493013571086263243059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2195662009047390842162039 3293493013571086263243059)
              ·
                refine ⟨4940239520356629394864589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3293493013571086263243059 4940239520356629394864589)
                ·
                  refine ⟨1852589820133736023074221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4940239520356629394864589 1852589820133736023074221)
                  ·
                    refine ⟨694721182550151008652833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1852589820133736023074221 694721182550151008652833)
                    ·
                      rfl

theorem cell22_2029447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_2029447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029447 prefixEnd_2029447 := by exact prefixLift 2029447
  have htrace : WordTrace (prefixWord ++ tailWord_2029447) baseStart_2029447 baseEnd_2029447 := by
    simpa [prefixWord, tailWord_2029447, baseEnd_2029447] using wordTrace_append hprefix tailTrace_2029447
  have hstable : (prefixWord ++ tailWord_2029447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029447).length < 2 ^ (prefixWord ++ tailWord_2029447).sum := by decide
  have hdescent : baseEnd_2029447 < baseStart_2029447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029460 : List Nat := [2, 4, 2, 1, 1, 2, 4, 1, 5]
def baseStart_2029460 : Nat := 118140960795 + 2029460 * 2 ^ 59
def prefixEnd_2029460 : Nat := 4983230072969 + 3 ^ 40 * 2029460 * 2
def baseEnd_2029460 : Nat := 231575210905274436025931

theorem tailTrace_2029460 : CollatzResearch.WordTrace tailWord_2029460 prefixEnd_2029460 231575210905274436025931 := by
  unfold tailWord_2029460
  simp only [CollatzResearch.WordTrace]
  refine ⟨37010243613810249509270917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49346991485080332679027889 37010243613810249509270917)
  ·
    refine ⟨6939420677589421782988297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37010243613810249509270917 6939420677589421782988297)
    ·
      refine ⟨5204565508192066337241223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6939420677589421782988297 5204565508192066337241223)
      ·
        refine ⟨7806848262288099505861835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5204565508192066337241223 7806848262288099505861835)
        ·
          refine ⟨11710272393432149258792753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7806848262288099505861835 11710272393432149258792753)
          ·
            refine ⟨8782704295074111944094565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11710272393432149258792753 8782704295074111944094565)
            ·
              refine ⟨1646757055326395989517731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8782704295074111944094565 1646757055326395989517731)
              ·
                refine ⟨2470135582989593984276597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646757055326395989517731 2470135582989593984276597)
                ·
                  refine ⟨231575210905274436025931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2470135582989593984276597 231575210905274436025931)
                  ·
                    rfl

theorem cell22_2029460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_2029460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029460 prefixEnd_2029460 := by exact prefixLift 2029460
  have htrace : WordTrace (prefixWord ++ tailWord_2029460) baseStart_2029460 baseEnd_2029460 := by
    simpa [prefixWord, tailWord_2029460, baseEnd_2029460] using wordTrace_append hprefix tailTrace_2029460
  have hstable : (prefixWord ++ tailWord_2029460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029460).length < 2 ^ (prefixWord ++ tailWord_2029460).sum := by decide
  have hdescent : baseEnd_2029460 < baseStart_2029460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029535 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 2, 4]
def baseStart_2029535 : Nat := 118140960795 + 2029535 * 2 ^ 59
def prefixEnd_2029535 : Nat := 4983230072969 + 3 ^ 40 * 2029535 * 2
def baseEnd_2029535 : Nat := 694751306748548112452563

theorem tailTrace_2029535 : CollatzResearch.WordTrace tailWord_2029535 prefixEnd_2029535 694751306748548112452563 := by
  unfold tailWord_2029535
  simp only [CollatzResearch.WordTrace]
  refine ⟨74023222702348786827522059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49348815134899191218348039 74023222702348786827522059)
  ·
    refine ⟨111034834053523180241283089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74023222702348786827522059 111034834053523180241283089)
    ·
      refine ⟨83276125540142385180962317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111034834053523180241283089 83276125540142385180962317)
      ·
        refine ⟨31228547077553394442860869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83276125540142385180962317 31228547077553394442860869)
        ·
          refine ⟨5855352577041261458036413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31228547077553394442860869 5855352577041261458036413)
          ·
            refine ⟨2195757216390473046763655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5855352577041261458036413 2195757216390473046763655)
            ·
              refine ⟨3293635824585709570145483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2195757216390473046763655 3293635824585709570145483)
              ·
                refine ⟨4940453736878564355218225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3293635824585709570145483 4940453736878564355218225)
                ·
                  refine ⟨3705340302658923266413669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4940453736878564355218225 3705340302658923266413669)
                  ·
                    refine ⟨694751306748548112452563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3705340302658923266413669 694751306748548112452563)
                    ·
                      rfl

theorem cell22_2029535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 4].length) (baseStart_2029535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029535 prefixEnd_2029535 := by exact prefixLift 2029535
  have htrace : WordTrace (prefixWord ++ tailWord_2029535) baseStart_2029535 baseEnd_2029535 := by
    simpa [prefixWord, tailWord_2029535, baseEnd_2029535] using wordTrace_append hprefix tailTrace_2029535
  have hstable : (prefixWord ++ tailWord_2029535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029535).length < 2 ^ (prefixWord ++ tailWord_2029535).sum := by decide
  have hdescent : baseEnd_2029535 < baseStart_2029535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029623 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 6]
def baseStart_2029623 : Nat := 118140960795 + 2029623 * 2 ^ 59
def prefixEnd_2029623 : Nat := 4983230072969 + 3 ^ 40 * 2029623 * 2
def baseEnd_2029623 : Nat := 231593810315648405417431

theorem tailTrace_2029623 : CollatzResearch.WordTrace tailWord_2029623 prefixEnd_2029623 231593810315648405417431 := by
  unfold tailWord_2029623
  simp only [CollatzResearch.WordTrace]
  refine ⟨74026432326029977856725523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49350954884019985237817015 74026432326029977856725523)
  ·
    refine ⟨111039648489044966785088285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74026432326029977856725523 111039648489044966785088285)
    ·
      refine ⟨41639868183391862544408107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111039648489044966785088285 41639868183391862544408107)
      ·
        refine ⟨62459802275087793816612161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41639868183391862544408107 62459802275087793816612161)
        ·
          refine ⟨46844851706315845362459121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62459802275087793816612161 46844851706315845362459121)
          ·
            refine ⟨35133638779736884021844341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46844851706315845362459121 35133638779736884021844341)
            ·
              refine ⟨3293778635600332877047907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35133638779736884021844341 3293778635600332877047907)
              ·
                refine ⟨4940667953400499315571861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3293778635600332877047907 4940667953400499315571861)
                ·
                  refine ⟨231593810315648405417431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4940667953400499315571861 231593810315648405417431)
                  ·
                    rfl

theorem cell22_2029623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 6].length) (baseStart_2029623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029623 prefixEnd_2029623 := by exact prefixLift 2029623
  have htrace : WordTrace (prefixWord ++ tailWord_2029623) baseStart_2029623 baseEnd_2029623 := by
    simpa [prefixWord, tailWord_2029623, baseEnd_2029623] using wordTrace_append hprefix tailTrace_2029623
  have hstable : (prefixWord ++ tailWord_2029623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029623).length < 2 ^ (prefixWord ++ tailWord_2029623).sum := by decide
  have hdescent : baseEnd_2029623 < baseStart_2029623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029820 : List Nat := [2, 2, 2, 1, 4, 1, 2, 8]
def baseStart_2029820 : Nat := 118140960795 + 2029820 * 2 ^ 59
def prefixEnd_2029820 : Nat := 4983230072969 + 3 ^ 40 * 2029820 * 2
def baseEnd_2029820 : Nat := 77205429785878041008521

theorem tailTrace_2029820 : CollatzResearch.WordTrace tailWord_2029820 prefixEnd_2029820 77205429785878041008521 := by
  unfold tailWord_2029820
  simp only [CollatzResearch.WordTrace]
  refine ⟨37016808753158140250823457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49355745004210853667764609 37016808753158140250823457)
  ·
    refine ⟨27762606564868605188117593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37016808753158140250823457 27762606564868605188117593)
    ·
      refine ⟨20821954923651453891088195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27762606564868605188117593 20821954923651453891088195)
      ·
        refine ⟨31232932385477180836632293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20821954923651453891088195 31232932385477180836632293)
        ·
          refine ⟨5856174822276971406868555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31232932385477180836632293 5856174822276971406868555)
          ·
            refine ⟨8784262233415457110302833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856174822276971406868555 8784262233415457110302833)
            ·
              refine ⟨6588196675061592832727125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8784262233415457110302833 6588196675061592832727125)
              ·
                refine ⟨77205429785878041008521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6588196675061592832727125 77205429785878041008521)
                ·
                  rfl

theorem cell22_2029820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 8].length) (baseStart_2029820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029820 prefixEnd_2029820 := by exact prefixLift 2029820
  have htrace : WordTrace (prefixWord ++ tailWord_2029820) baseStart_2029820 baseEnd_2029820 := by
    simpa [prefixWord, tailWord_2029820, baseEnd_2029820] using wordTrace_append hprefix tailTrace_2029820
  have hstable : (prefixWord ++ tailWord_2029820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029820).length < 2 ^ (prefixWord ++ tailWord_2029820).sum := by decide
  have hdescent : baseEnd_2029820 < baseStart_2029820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029852 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 3, 3]
def baseStart_2029852 : Nat := 118140960795 + 2029852 * 2 ^ 59
def prefixEnd_2029852 : Nat := 4983230072969 + 3 ^ 40 * 2029852 * 2
def baseEnd_2029852 : Nat := 694859822326864952276591

theorem tailTrace_2029852 : CollatzResearch.WordTrace tailWord_2029852 prefixEnd_2029852 694859822326864952276591 := by
  unfold tailWord_2029852
  simp only [CollatzResearch.WordTrace]
  refine ⟨37017392321100174983405905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49356523094800233311207873 37017392321100174983405905)
  ·
    refine ⟨27763044240825131237554429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37017392321100174983405905 27763044240825131237554429)
    ·
      refine ⟨10411141590309424214082911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27763044240825131237554429 10411141590309424214082911)
      ·
        refine ⟨15616712385464136321124367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10411141590309424214082911 15616712385464136321124367)
        ·
          refine ⟨23425068578196204481686551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15616712385464136321124367 23425068578196204481686551)
          ·
            refine ⟨35137602867294306722529827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23425068578196204481686551 35137602867294306722529827)
            ·
              refine ⟨52706404300941460083794741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35137602867294306722529827 52706404300941460083794741)
              ·
                refine ⟨4941225403213261882855757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52706404300941460083794741 4941225403213261882855757)
                ·
                  refine ⟨1852959526204973206070909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4941225403213261882855757 1852959526204973206070909)
                  ·
                    refine ⟨694859822326864952276591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1852959526204973206070909 694859822326864952276591)
                    ·
                      rfl

theorem cell22_2029852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_2029852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029852 prefixEnd_2029852 := by exact prefixLift 2029852
  have htrace : WordTrace (prefixWord ++ tailWord_2029852) baseStart_2029852 baseEnd_2029852 := by
    simpa [prefixWord, tailWord_2029852, baseEnd_2029852] using wordTrace_append hprefix tailTrace_2029852
  have hstable : (prefixWord ++ tailWord_2029852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029852).length < 2 ^ (prefixWord ++ tailWord_2029852).sum := by decide
  have hdescent : baseEnd_2029852 < baseStart_2029852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029854 : List Nat := [4, 3, 2, 1, 1, 1, 3, 7]
def baseStart_2029854 : Nat := 118140960795 + 2029854 * 2 ^ 59
def prefixEnd_2029854 : Nat := 4983230072969 + 3 ^ 40 * 2029854 * 2
def baseEnd_2029854 : Nat := 77206722996415290414065

theorem tailTrace_2029854 : CollatzResearch.WordTrace tailWord_2029854 prefixEnd_2029854 77206722996415290414065 := by
  unfold tailWord_2029854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9254357198524138038548077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49356571725462069538923077 9254357198524138038548077)
  ·
    refine ⟨3470383949446551764455529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9254357198524138038548077 3470383949446551764455529)
    ·
      refine ⟨2602787962084913823341647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3470383949446551764455529 2602787962084913823341647)
      ·
        refine ⟨3904181943127370735012471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2602787962084913823341647 3904181943127370735012471)
        ·
          refine ⟨5856272914691056102518707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3904181943127370735012471 5856272914691056102518707)
          ·
            refine ⟨8784409372036584153778061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856272914691056102518707 8784409372036584153778061)
            ·
              refine ⟨3294153514513719057666773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8784409372036584153778061 3294153514513719057666773)
              ·
                refine ⟨77206722996415290414065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3294153514513719057666773 77206722996415290414065)
                ·
                  rfl

theorem cell22_2029854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_2029854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029854 prefixEnd_2029854 := by exact prefixLift 2029854
  have htrace : WordTrace (prefixWord ++ tailWord_2029854) baseStart_2029854 baseEnd_2029854 := by
    simpa [prefixWord, tailWord_2029854, baseEnd_2029854] using wordTrace_append hprefix tailTrace_2029854
  have hstable : (prefixWord ++ tailWord_2029854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029854).length < 2 ^ (prefixWord ++ tailWord_2029854).sum := by decide
  have hdescent : baseEnd_2029854 < baseStart_2029854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029886 : List Nat := [4, 2, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_2029886 : Nat := 118140960795 + 2029886 * 2 ^ 59
def prefixEnd_2029886 : Nat := 4983230072969 + 3 ^ 40 * 2029886 * 2
def baseEnd_2029886 : Nat := 694871461221700196926487

theorem tailTrace_2029886 : CollatzResearch.WordTrace tailWord_2029886 prefixEnd_2029886 694871461221700196926487 := by
  unfold tailWord_2029886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9254503090509646721693689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49357349816051449182366341 9254503090509646721693689)
  ·
    refine ⟨6940877317882235041270267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9254503090509646721693689 6940877317882235041270267)
    ·
      refine ⟨10411315976823352561905401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6940877317882235041270267 10411315976823352561905401)
      ·
        refine ⟨7808486982617514421429051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10411315976823352561905401 7808486982617514421429051)
        ·
          refine ⟨11712730473926271632143577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7808486982617514421429051 11712730473926271632143577)
          ·
            refine ⟨8784547855444703724107683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11712730473926271632143577 8784547855444703724107683)
            ·
              refine ⟨13176821783167055586161525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8784547855444703724107683 13176821783167055586161525)
              ·
                refine ⟨1235327042171911461202643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13176821783167055586161525 1235327042171911461202643)
                ·
                  refine ⟨1852990563257867191803965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235327042171911461202643 1852990563257867191803965)
                  ·
                    refine ⟨694871461221700196926487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1852990563257867191803965 694871461221700196926487)
                    ·
                      rfl

theorem cell22_2029886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_2029886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029886 prefixEnd_2029886 := by exact prefixLift 2029886
  have htrace : WordTrace (prefixWord ++ tailWord_2029886) baseStart_2029886 baseEnd_2029886 := by
    simpa [prefixWord, tailWord_2029886, baseEnd_2029886] using wordTrace_append hprefix tailTrace_2029886
  have hstable : (prefixWord ++ tailWord_2029886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029886).length < 2 ^ (prefixWord ++ tailWord_2029886).sum := by decide
  have hdescent : baseEnd_2029886 < baseStart_2029886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029927 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 6]
def baseStart_2029927 : Nat := 118140960795 + 2029927 * 2 ^ 59
def prefixEnd_2029927 : Nat := 4983230072969 + 3 ^ 40 * 2029927 * 2
def baseEnd_2029927 : Nat := 231628498786529918883787

theorem tailTrace_2029927 : CollatzResearch.WordTrace tailWord_2029927 prefixEnd_2029927 231628498786529918883787 := by
  unfold tailWord_2029927
  simp only [CollatzResearch.WordTrace]
  refine ⟨74037520116928637775792035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49358346744619091850528023 74037520116928637775792035)
  ·
    refine ⟨111056280175392956663688053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74037520116928637775792035 111056280175392956663688053)
    ·
      refine ⟨10411526266443089687220755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111056280175392956663688053 10411526266443089687220755)
      ·
        refine ⟨15617289399664634530831133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10411526266443089687220755 15617289399664634530831133)
        ·
          refine ⟨5856483524874237949061675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15617289399664634530831133 5856483524874237949061675)
          ·
            refine ⟨8784725287311356923592513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856483524874237949061675 8784725287311356923592513)
            ·
              refine ⟨6588543965483517692694385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8784725287311356923592513 6588543965483517692694385)
              ·
                refine ⟨4941407974112638269520789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6588543965483517692694385 4941407974112638269520789)
                ·
                  refine ⟨231628498786529918883787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4941407974112638269520789 231628498786529918883787)
                  ·
                    rfl

theorem cell22_2029927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 6].length) (baseStart_2029927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029927 prefixEnd_2029927 := by exact prefixLift 2029927
  have htrace : WordTrace (prefixWord ++ tailWord_2029927) baseStart_2029927 baseEnd_2029927 := by
    simpa [prefixWord, tailWord_2029927, baseEnd_2029927] using wordTrace_append hprefix tailTrace_2029927
  have hstable : (prefixWord ++ tailWord_2029927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029927).length < 2 ^ (prefixWord ++ tailWord_2029927).sum := by decide
  have hdescent : baseEnd_2029927 < baseStart_2029927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029959 : List Nat := [1, 1, 4, 2, 2, 1, 2, 4, 2, 3]
def baseStart_2029959 : Nat := 118140960795 + 2029959 * 2 ^ 59
def prefixEnd_2029959 : Nat := 4983230072969 + 3 ^ 40 * 2029959 * 2
def baseEnd_2029959 : Nat := 694896450613552339851263

theorem tailTrace_2029959 : CollatzResearch.WordTrace tailWord_2029959 prefixEnd_2029959 694896450613552339851263 := by
  unfold tailWord_2029959
  simp only [CollatzResearch.WordTrace]
  refine ⟨74038687252812707240956931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49359124835208471493971287 74038687252812707240956931)
  ·
    refine ⟨111058030879219060861435397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74038687252812707240956931 111058030879219060861435397)
    ·
      refine ⟨20823380789853573911519137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111058030879219060861435397 20823380789853573911519137)
      ·
        refine ⟨15617535592390180433639353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20823380789853573911519137 15617535592390180433639353)
        ·
          refine ⟨11713151694292635325229515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15617535592390180433639353 11713151694292635325229515)
          ·
            refine ⟨17569727541438952987844273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11713151694292635325229515 17569727541438952987844273)
            ·
              refine ⟨13177295656079214740883205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17569727541438952987844273 13177295656079214740883205)
              ·
                refine ⟨2470742935514852763915601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13177295656079214740883205 2470742935514852763915601)
                ·
                  refine ⟨1853057201636139572936701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2470742935514852763915601 1853057201636139572936701)
                  ·
                    refine ⟨694896450613552339851263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1853057201636139572936701 694896450613552339851263)
                    ·
                      rfl

theorem cell22_2029959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_2029959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029959 prefixEnd_2029959 := by exact prefixLift 2029959
  have htrace : WordTrace (prefixWord ++ tailWord_2029959) baseStart_2029959 baseEnd_2029959 := by
    simpa [prefixWord, tailWord_2029959, baseEnd_2029959] using wordTrace_append hprefix tailTrace_2029959
  have hstable : (prefixWord ++ tailWord_2029959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029959).length < 2 ^ (prefixWord ++ tailWord_2029959).sum := by decide
  have hdescent : baseEnd_2029959 < baseStart_2029959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029961 : List Nat := [1, 2, 1, 1, 6, 2, 3, 2, 4]
def baseStart_2029961 : Nat := 118140960795 + 2029961 * 2 ^ 59
def prefixEnd_2029961 : Nat := 4983230072969 + 3 ^ 40 * 2029961 * 2
def baseEnd_2029961 : Nat := 231632378418141667100419

theorem tailTrace_2029961 : CollatzResearch.WordTrace tailWord_2029961 prefixEnd_2029961 231632378418141667100419 := by
  unfold tailWord_2029961
  simp only [CollatzResearch.WordTrace]
  refine ⟨74038760198805461582529737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49359173465870307721686491 74038760198805461582529737)
  ·
    refine ⟨55529070149104096186897303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74038760198805461582529737 55529070149104096186897303)
    ·
      refine ⟨83293605223656144280345955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55529070149104096186897303 83293605223656144280345955)
      ·
        refine ⟨124940407835484216420518933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83293605223656144280345955 124940407835484216420518933)
        ·
          refine ⟨5856581617288322644711825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 124940407835484216420518933 5856581617288322644711825)
          ·
            refine ⟨4392436212966241983533869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5856581617288322644711825 4392436212966241983533869)
            ·
              refine ⟨1647163579862340743825201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4392436212966241983533869 1647163579862340743825201)
              ·
                refine ⟨1235372684896755557868901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647163579862340743825201 1235372684896755557868901)
                ·
                  refine ⟨231632378418141667100419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1235372684896755557868901 231632378418141667100419)
                  ·
                    rfl

theorem cell22_2029961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 4].length) (baseStart_2029961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029961 prefixEnd_2029961 := by exact prefixLift 2029961
  have htrace : WordTrace (prefixWord ++ tailWord_2029961) baseStart_2029961 baseEnd_2029961 := by
    simpa [prefixWord, tailWord_2029961, baseEnd_2029961] using wordTrace_append hprefix tailTrace_2029961
  have hstable : (prefixWord ++ tailWord_2029961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029961).length < 2 ^ (prefixWord ++ tailWord_2029961).sum := by decide
  have hdescent : baseEnd_2029961 < baseStart_2029961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029976 : List Nat := [2, 1, 2, 5, 1, 2, 1, 3, 2, 3]
def baseStart_2029976 : Nat := 118140960795 + 2029976 * 2 ^ 59
def prefixEnd_2029976 : Nat := 4983230072969 + 3 ^ 40 * 2029976 * 2
def baseEnd_2029976 : Nat := 694902270060969962176211

theorem tailTrace_2029976 : CollatzResearch.WordTrace tailWord_2029976 prefixEnd_2029976 694902270060969962176211 := by
  unfold tailWord_2029976
  simp only [CollatzResearch.WordTrace]
  refine ⟨37019653646875559572162891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49359538195834079429550521 37019653646875559572162891)
  ·
    refine ⟨55529480470313339358244337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37019653646875559572162891 55529480470313339358244337)
    ·
      refine ⟨41647110352735004518683253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55529480470313339358244337 41647110352735004518683253)
      ·
        refine ⟨3904416595568906673626555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41647110352735004518683253 3904416595568906673626555)
        ·
          refine ⟨5856624893353360010439833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3904416595568906673626555 5856624893353360010439833)
          ·
            refine ⟨4392468670015020007829875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5856624893353360010439833 4392468670015020007829875)
            ·
              refine ⟨6588703005022530011744813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392468670015020007829875 6588703005022530011744813)
              ·
                refine ⟨2470763626883448754404305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6588703005022530011744813 2470763626883448754404305)
                ·
                  refine ⟨1853072720162586565803229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2470763626883448754404305 1853072720162586565803229)
                  ·
                    refine ⟨694902270060969962176211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1853072720162586565803229 694902270060969962176211)
                    ·
                      rfl

theorem cell22_2029976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_2029976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2029976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2029976 prefixEnd_2029976 := by exact prefixLift 2029976
  have htrace : WordTrace (prefixWord ++ tailWord_2029976) baseStart_2029976 baseEnd_2029976 := by
    simpa [prefixWord, tailWord_2029976, baseEnd_2029976] using wordTrace_append hprefix tailTrace_2029976
  have hstable : (prefixWord ++ tailWord_2029976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029976).length < 2 ^ (prefixWord ++ tailWord_2029976).sum := by decide
  have hdescent : baseEnd_2029976 < baseStart_2029976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030064 : List Nat := [2, 1, 1, 1, 3, 3, 3, 3, 1, 4]
def baseStart_2030064 : Nat := 118140960795 + 2030064 * 2 ^ 59
def prefixEnd_2030064 : Nat := 4983230072969 + 3 ^ 40 * 2030064 * 2
def baseEnd_2030064 : Nat := 694932394259367065975941

theorem tailTrace_2030064 : CollatzResearch.WordTrace tailWord_2030064 prefixEnd_2030064 694932394259367065975941 := by
  unfold tailWord_2030064
  simp only [CollatzResearch.WordTrace]
  refine ⟨37021258458716155086764623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49361677944954873449019497 37021258458716155086764623)
  ·
    refine ⟨55531887688074232630146935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37021258458716155086764623 55531887688074232630146935)
    ·
      refine ⟨83297831532111348945220403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55531887688074232630146935 83297831532111348945220403)
      ·
        refine ⟨124946747298167023417830605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83297831532111348945220403 124946747298167023417830605)
        ·
          refine ⟨46855030236812633781686477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124946747298167023417830605 46855030236812633781686477)
          ·
            refine ⟨17570636338804737668132429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46855030236812633781686477 17570636338804737668132429)
            ·
              refine ⟨6588988627051776625549661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17570636338804737668132429 6588988627051776625549661)
              ·
                refine ⟨2470870735144416234581123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6588988627051776625549661 2470870735144416234581123)
                ·
                  refine ⟨3706306102716624351871685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2470870735144416234581123 3706306102716624351871685)
                  ·
                    refine ⟨694932394259367065975941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3706306102716624351871685 694932394259367065975941)
                    ·
                      rfl

theorem cell22_2030064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_2030064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030064 prefixEnd_2030064 := by exact prefixLift 2030064
  have htrace : WordTrace (prefixWord ++ tailWord_2030064) baseStart_2030064 baseEnd_2030064 := by
    simpa [prefixWord, tailWord_2030064, baseEnd_2030064] using wordTrace_append hprefix tailTrace_2030064
  have hstable : (prefixWord ++ tailWord_2030064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030064).length < 2 ^ (prefixWord ++ tailWord_2030064).sum := by decide
  have hdescent : baseEnd_2030064 < baseStart_2030064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030079 : List Nat := [1, 1, 2, 2, 1, 2, 3, 6, 4]
def baseStart_2030079 : Nat := 118140960795 + 2030079 * 2 ^ 59
def prefixEnd_2030079 : Nat := 4983230072969 + 3 ^ 40 * 2030079 * 2
def baseEnd_2030079 : Nat := 231645843021970675616965

theorem tailTrace_2030079 : CollatzResearch.WordTrace tailWord_2030079 prefixEnd_2030079 231645843021970675616965 := by
  unfold tailWord_2030079
  simp only [CollatzResearch.WordTrace]
  refine ⟨74043064012377967735325291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49362042674918645156883527 74043064012377967735325291)
  ·
    refine ⟨111064596018566951602987937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74043064012377967735325291 111064596018566951602987937)
    ·
      refine ⟨83298447013925213702240953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111064596018566951602987937 83298447013925213702240953)
      ·
        refine ⟨62473835260443910276680715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83298447013925213702240953 62473835260443910276680715)
        ·
          refine ⟨93710752890665865415021073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62473835260443910276680715 93710752890665865415021073)
          ·
            refine ⟨70283064667999399061265805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93710752890665865415021073 70283064667999399061265805)
            ·
              refine ⟨26356149250499774647974677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70283064667999399061265805 26356149250499774647974677)
              ·
                refine ⟨1235444496117176936623813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26356149250499774647974677 1235444496117176936623813)
                ·
                  refine ⟨231645843021970675616965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1235444496117176936623813 231645843021970675616965)
                  ·
                    rfl

theorem cell22_2030079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 4].length) (baseStart_2030079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030079 prefixEnd_2030079 := by exact prefixLift 2030079
  have htrace : WordTrace (prefixWord ++ tailWord_2030079) baseStart_2030079 baseEnd_2030079 := by
    simpa [prefixWord, tailWord_2030079, baseEnd_2030079] using wordTrace_append hprefix tailTrace_2030079
  have hstable : (prefixWord ++ tailWord_2030079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030079).length < 2 ^ (prefixWord ++ tailWord_2030079).sum := by decide
  have hdescent : baseEnd_2030079 < baseStart_2030079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030109 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_2030109 : Nat := 118140960795 + 2030109 * 2 ^ 59
def prefixEnd_2030109 : Nat := 4983230072969 + 3 ^ 40 * 2030109 * 2
def baseEnd_2030109 : Nat := 694947798679001948600803

theorem tailTrace_2030109 : CollatzResearch.WordTrace tailWord_2030109 prefixEnd_2030109 694947798679001948600803 := by
  unfold tailWord_2030109
  simp only [CollatzResearch.WordTrace]
  refine ⟨74044158202269282858917381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49362772134846188572611587 74044158202269282858917381)
  ·
    refine ⟨13883279662925490536047009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74044158202269282858917381 13883279662925490536047009)
    ·
      refine ⟨10412459747194117902035257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13883279662925490536047009 10412459747194117902035257)
      ·
        refine ⟨7809344810395588426526443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10412459747194117902035257 7809344810395588426526443)
        ·
          refine ⟨11714017215593382639789665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809344810395588426526443 11714017215593382639789665)
          ·
            refine ⟨8785512911695036979842249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11714017215593382639789665 8785512911695036979842249)
            ·
              refine ⟨6589134683771277734881687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8785512911695036979842249 6589134683771277734881687)
              ·
                refine ⟨9883702025656916602322531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6589134683771277734881687 9883702025656916602322531)
                ·
                  refine ⟨14825553038485374903483797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9883702025656916602322531 14825553038485374903483797)
                  ·
                    refine ⟨694947798679001948600803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14825553038485374903483797 694947798679001948600803)
                    ·
                      rfl

theorem cell22_2030109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_2030109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030109 prefixEnd_2030109 := by exact prefixLift 2030109
  have htrace : WordTrace (prefixWord ++ tailWord_2030109) baseStart_2030109 baseEnd_2030109 := by
    simpa [prefixWord, tailWord_2030109, baseEnd_2030109] using wordTrace_append hprefix tailTrace_2030109
  have hstable : (prefixWord ++ tailWord_2030109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030109).length < 2 ^ (prefixWord ++ tailWord_2030109).sum := by decide
  have hdescent : baseEnd_2030109 < baseStart_2030109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030145 : List Nat := [1, 2, 5, 1, 1, 4, 2, 1, 2, 3]
def baseStart_2030145 : Nat := 118140960795 + 2030145 * 2 ^ 59
def prefixEnd_2030145 : Nat := 4983230072969 + 3 ^ 40 * 2030145 * 2
def baseEnd_2030145 : Nat := 694960122214709854700693

theorem tailTrace_2030145 : CollatzResearch.WordTrace tailWord_2030145 prefixEnd_2030145 694960122214709854700693 := by
  unfold tailWord_2030145
  simp only [CollatzResearch.WordTrace]
  refine ⟨74045471230138861007227889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49363647486759240671485259 74045471230138861007227889)
  ·
    refine ⟨55534103422604145755420917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74045471230138861007227889 55534103422604145755420917)
    ·
      refine ⟨5206322195869138664570711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55534103422604145755420917 5206322195869138664570711)
      ·
        refine ⟨7809483293803707996856067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5206322195869138664570711 7809483293803707996856067)
        ·
          refine ⟨11714224940705561995284101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809483293803707996856067 11714224940705561995284101)
          ·
            refine ⟨2196417176382292874115769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11714224940705561995284101 2196417176382292874115769)
            ·
              refine ⟨1647312882286719655586827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2196417176382292874115769 1647312882286719655586827)
              ·
                refine ⟨2470969323430079483380241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647312882286719655586827 2470969323430079483380241)
                ·
                  refine ⟨1853226992572559612535181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2470969323430079483380241 1853226992572559612535181)
                  ·
                    refine ⟨694960122214709854700693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1853226992572559612535181 694960122214709854700693)
                    ·
                      rfl

theorem cell22_2030145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_2030145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030145 prefixEnd_2030145 := by exact prefixLift 2030145
  have htrace : WordTrace (prefixWord ++ tailWord_2030145) baseStart_2030145 baseEnd_2030145 := by
    simpa [prefixWord, tailWord_2030145, baseEnd_2030145] using wordTrace_append hprefix tailTrace_2030145
  have hstable : (prefixWord ++ tailWord_2030145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030145).length < 2 ^ (prefixWord ++ tailWord_2030145).sum := by decide
  have hdescent : baseEnd_2030145 < baseStart_2030145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030186 : List Nat := [3, 1, 3, 2, 1, 1, 4, 2, 5]
def baseStart_2030186 : Nat := 118140960795 + 2030186 * 2 ^ 59
def prefixEnd_2030186 : Nat := 4983230072969 + 3 ^ 40 * 2030186 * 2
def baseEnd_2030186 : Nat := 231658052450866471475189

theorem tailTrace_2030186 : CollatzResearch.WordTrace tailWord_2030186 prefixEnd_2030186 231658052450866471475189 := by
  unfold tailWord_2030186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18511741655747581252367603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49364644415326883339646941 18511741655747581252367603)
  ·
    refine ⟨27767612483621371878551405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18511741655747581252367603 27767612483621371878551405)
    ·
      refine ⟨10412854681358014454456777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27767612483621371878551405 10412854681358014454456777)
      ·
        refine ⟨7809641011018510840842583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10412854681358014454456777 7809641011018510840842583)
        ·
          refine ⟨11714461516527766261263875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809641011018510840842583 11714461516527766261263875)
          ·
            refine ⟨17571692274791649391895813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11714461516527766261263875 17571692274791649391895813)
            ·
              refine ⟨3294692301523434260980465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17571692274791649391895813 3294692301523434260980465)
              ·
                refine ⟨2471019226142575695735349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3294692301523434260980465 2471019226142575695735349)
                ·
                  refine ⟨231658052450866471475189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2471019226142575695735349 231658052450866471475189)
                  ·
                    rfl

theorem cell22_2030186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_2030186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030186 prefixEnd_2030186 := by exact prefixLift 2030186
  have htrace : WordTrace (prefixWord ++ tailWord_2030186) baseStart_2030186 baseEnd_2030186 := by
    simpa [prefixWord, tailWord_2030186, baseEnd_2030186] using wordTrace_append hprefix tailTrace_2030186
  have hstable : (prefixWord ++ tailWord_2030186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030186).length < 2 ^ (prefixWord ++ tailWord_2030186).sum := by decide
  have hdescent : baseEnd_2030186 < baseStart_2030186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030190 : List Nat := [4, 1, 2, 2, 2, 2, 1, 4, 1, 3]
def baseStart_2030190 : Nat := 118140960795 + 2030190 * 2 ^ 59
def prefixEnd_2030190 : Nat := 4983230072969 + 3 ^ 40 * 2030190 * 2
def baseEnd_2030190 : Nat := 694975526634344737325555

theorem tailTrace_2030190 : CollatzResearch.WordTrace tailWord_2030190 prefixEnd_2030190 694975526634344737325555 := by
  unfold tailWord_2030190
  simp only [CollatzResearch.WordTrace]
  refine ⟨9255889064371979211577003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49364741676650555795077349 9255889064371979211577003)
  ·
    refine ⟨13883833596557968817365505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9255889064371979211577003 13883833596557968817365505)
    ·
      refine ⟨10412875197418476613024129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13883833596557968817365505 10412875197418476613024129)
      ·
        refine ⟨7809656398063857459768097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10412875197418476613024129 7809656398063857459768097)
        ·
          refine ⟨5857242298547893094826073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7809656398063857459768097 5857242298547893094826073)
          ·
            refine ⟨4392931723910919821119555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5857242298547893094826073 4392931723910919821119555)
            ·
              refine ⟨6589397585866379731679333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392931723910919821119555 6589397585866379731679333)
              ·
                refine ⟨1235512047349946199689875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6589397585866379731679333 1235512047349946199689875)
                ·
                  refine ⟨1853268071024919299534813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235512047349946199689875 1853268071024919299534813)
                  ·
                    refine ⟨694975526634344737325555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1853268071024919299534813 694975526634344737325555)
                    ·
                      rfl

theorem cell22_2030190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_2030190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030190 prefixEnd_2030190 := by exact prefixLift 2030190
  have htrace : WordTrace (prefixWord ++ tailWord_2030190) baseStart_2030190 baseEnd_2030190 := by
    simpa [prefixWord, tailWord_2030190, baseEnd_2030190] using wordTrace_append hprefix tailTrace_2030190
  have hstable : (prefixWord ++ tailWord_2030190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030190).length < 2 ^ (prefixWord ++ tailWord_2030190).sum := by decide
  have hdescent : baseEnd_2030190 < baseStart_2030190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030199 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 3, 4]
def baseStart_2030199 : Nat := 118140960795 + 2030199 * 2 ^ 59
def prefixEnd_2030199 : Nat := 4983230072969 + 3 ^ 40 * 2030199 * 2
def baseEnd_2030199 : Nat := 694978607518271713850527

theorem tailTrace_2030199 : CollatzResearch.WordTrace tailWord_2030199 prefixEnd_2030199 694978607518271713850527 := by
  unfold tailWord_2030199
  simp only [CollatzResearch.WordTrace]
  refine ⟨74047440771943228229693651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49364960514628818819795767 74047440771943228229693651)
  ·
    refine ⟨111071161157914842344540477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74047440771943228229693651 111071161157914842344540477)
    ·
      refine ⟨41651685434218065879202679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111071161157914842344540477 41651685434218065879202679)
      ·
        refine ⟨62477528151327098818804019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41651685434218065879202679 62477528151327098818804019)
        ·
          refine ⟨93716292226990648228206029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62477528151327098818804019 93716292226990648228206029)
          ·
            refine ⟨35143609585121493085577261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93716292226990648228206029 35143609585121493085577261)
            ·
              refine ⟨13178853594420559907091473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35143609585121493085577261 13178853594420559907091473)
              ·
                refine ⟨9884140195815419930318605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13178853594420559907091473 9884140195815419930318605)
                ·
                  refine ⟨3706552573430782473869477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9884140195815419930318605 3706552573430782473869477)
                  ·
                    refine ⟨694978607518271713850527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3706552573430782473869477 694978607518271713850527)
                    ·
                      rfl

theorem cell22_2030199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_2030199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030199 prefixEnd_2030199 := by exact prefixLift 2030199
  have htrace : WordTrace (prefixWord ++ tailWord_2030199) baseStart_2030199 baseEnd_2030199 := by
    simpa [prefixWord, tailWord_2030199, baseEnd_2030199] using wordTrace_append hprefix tailTrace_2030199
  have hstable : (prefixWord ++ tailWord_2030199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030199).length < 2 ^ (prefixWord ++ tailWord_2030199).sum := by decide
  have hdescent : baseEnd_2030199 < baseStart_2030199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030261 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_2030261 : Nat := 118140960795 + 2030261 * 2 ^ 59
def prefixEnd_2030261 : Nat := 4983230072969 + 3 ^ 40 * 2030261 * 2
def baseEnd_2030261 : Nat := 694999831385324218800337

theorem tailTrace_2030261 : CollatzResearch.WordTrace tailWord_2030261 prefixEnd_2030261 694999831385324218800337 := by
  unfold tailWord_2030261
  simp only [CollatzResearch.WordTrace]
  refine ⟨74049702097718612818450637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49366468065145741878967091 74049702097718612818450637)
  ·
    refine ⟨27768638286644479806918989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74049702097718612818450637 27768638286644479806918989)
    ·
      refine ⟨10413239357491679927594621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27768638286644479806918989 10413239357491679927594621)
      ·
        refine ⟨3904964759059379972847983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10413239357491679927594621 3904964759059379972847983)
        ·
          refine ⟨5857447138589069959271975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3904964759059379972847983 5857447138589069959271975)
          ·
            refine ⟨8786170707883604938907963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5857447138589069959271975 8786170707883604938907963)
            ·
              refine ⟨13179256061825407408361945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8786170707883604938907963 13179256061825407408361945)
              ·
                refine ⟨9884442046369055556271459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13179256061825407408361945 9884442046369055556271459)
                ·
                  refine ⟨14826663069553583334407189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9884442046369055556271459 14826663069553583334407189)
                  ·
                    refine ⟨694999831385324218800337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14826663069553583334407189 694999831385324218800337)
                    ·
                      rfl

theorem cell22_2030261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_2030261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030261 prefixEnd_2030261 := by exact prefixLift 2030261
  have htrace : WordTrace (prefixWord ++ tailWord_2030261) baseStart_2030261 baseEnd_2030261 := by
    simpa [prefixWord, tailWord_2030261, baseEnd_2030261] using wordTrace_append hprefix tailTrace_2030261
  have hstable : (prefixWord ++ tailWord_2030261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030261).length < 2 ^ (prefixWord ++ tailWord_2030261).sum := by decide
  have hdescent : baseEnd_2030261 < baseStart_2030261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030263 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 1, 5]
def baseStart_2030263 : Nat := 118140960795 + 2030263 * 2 ^ 59
def prefixEnd_2030263 : Nat := 4983230072969 + 3 ^ 40 * 2030263 * 2
def baseEnd_2030263 : Nat := 695000516026196880250331

theorem tailTrace_2030263 : CollatzResearch.WordTrace tailWord_2030263 prefixEnd_2030263 695000516026196880250331 := by
  unfold tailWord_2030263
  simp only [CollatzResearch.WordTrace]
  refine ⟨74049775043711367160023443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49366516695807578106682295 74049775043711367160023443)
  ·
    refine ⟨111074662565567050740035165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74049775043711367160023443 111074662565567050740035165)
    ·
      refine ⟨41652998462087644027513187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111074662565567050740035165 41652998462087644027513187)
      ·
        refine ⟨62479497693131466041269781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41652998462087644027513187 62479497693131466041269781)
        ·
          refine ⟨2928726454365537470684521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62479497693131466041269781 2928726454365537470684521)
          ·
            refine ⟨2196544840774153103013391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2928726454365537470684521 2196544840774153103013391)
            ·
              refine ⟨3294817261161229654520087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2196544840774153103013391 3294817261161229654520087)
              ·
                refine ⟨4942225891741844481780131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3294817261161229654520087 4942225891741844481780131)
                ·
                  refine ⟨7413338837612766722670197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4942225891741844481780131 7413338837612766722670197)
                  ·
                    refine ⟨695000516026196880250331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7413338837612766722670197 695000516026196880250331)
                    ·
                      rfl

theorem cell22_2030263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_2030263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030263 prefixEnd_2030263 := by exact prefixLift 2030263
  have htrace : WordTrace (prefixWord ++ tailWord_2030263) baseStart_2030263 baseEnd_2030263 := by
    simpa [prefixWord, tailWord_2030263, baseEnd_2030263] using wordTrace_append hprefix tailTrace_2030263
  have hstable : (prefixWord ++ tailWord_2030263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030263).length < 2 ^ (prefixWord ++ tailWord_2030263).sum := by decide
  have hdescent : baseEnd_2030263 < baseStart_2030263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030276 : List Nat := [2, 3, 3, 1, 1, 3, 1, 8]
def baseStart_2030276 : Nat := 118140960795 + 2030276 * 2 ^ 59
def prefixEnd_2030276 : Nat := 4983230072969 + 3 ^ 40 * 2030276 * 2
def baseEnd_2030276 : Nat := 77222774021318797741699

theorem tailTrace_2030276 : CollatzResearch.WordTrace tailWord_2030276 prefixEnd_2030276 77222774021318797741699 := by
  unfold tailWord_2030276
  simp only [CollatzResearch.WordTrace]
  refine ⟨37025124596332135190123341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49366832795109513586831121 37025124596332135190123341)
  ·
    refine ⟨13884421723624550696296253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37025124596332135190123341 13884421723624550696296253)
    ·
      refine ⟨5206658146359206511111095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13884421723624550696296253 5206658146359206511111095)
      ·
        refine ⟨7809987219538809766666643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5206658146359206511111095 7809987219538809766666643)
        ·
          refine ⟨11714980829308214649999965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809987219538809766666643 11714980829308214649999965)
          ·
            refine ⟨4393117810990580493749987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11714980829308214649999965 4393117810990580493749987)
            ·
              refine ⟨6589676716485870740624981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4393117810990580493749987 6589676716485870740624981)
              ·
                refine ⟨77222774021318797741699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6589676716485870740624981 77222774021318797741699)
                ·
                  rfl

theorem cell22_2030276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 8].length) (baseStart_2030276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030276 prefixEnd_2030276 := by exact prefixLift 2030276
  have htrace : WordTrace (prefixWord ++ tailWord_2030276) baseStart_2030276 baseEnd_2030276 := by
    simpa [prefixWord, tailWord_2030276, baseEnd_2030276] using wordTrace_append hprefix tailTrace_2030276
  have hstable : (prefixWord ++ tailWord_2030276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030276).length < 2 ^ (prefixWord ++ tailWord_2030276).sum := by decide
  have hdescent : baseEnd_2030276 < baseStart_2030276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030293 : List Nat := [1, 3, 2, 5, 1, 2, 8]
def baseStart_2030293 : Nat := 118140960795 + 2030293 * 2 ^ 59
def prefixEnd_2030293 : Nat := 4983230072969 + 3 ^ 40 * 2030293 * 2
def baseEnd_2030293 : Nat := 25741140208862474148157

theorem tailTrace_2030293 : CollatzResearch.WordTrace tailWord_2030293 prefixEnd_2030293 25741140208862474148157 := by
  unfold tailWord_2030293
  simp only [CollatzResearch.WordTrace]
  refine ⟨74050869233602682283615533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49367246155735121522410355 74050869233602682283615533)
  ·
    refine ⟨27769075962601005856355825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74050869233602682283615533 27769075962601005856355825)
    ·
      refine ⟨20826806971950754392266869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27769075962601005856355825 20826806971950754392266869)
      ·
        refine ⟨1952513153620383224275019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20826806971950754392266869 1952513153620383224275019)
        ·
          refine ⟨2928769730430574836412529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952513153620383224275019 2928769730430574836412529)
          ·
            refine ⟨2196577297822931127309397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2928769730430574836412529 2196577297822931127309397)
            ·
              refine ⟨25741140208862474148157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2196577297822931127309397 25741140208862474148157)
              ·
                rfl

theorem cell22_2030293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 8].length) (baseStart_2030293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030293 prefixEnd_2030293 := by exact prefixLift 2030293
  have htrace : WordTrace (prefixWord ++ tailWord_2030293) baseStart_2030293 baseEnd_2030293 := by
    simpa [prefixWord, tailWord_2030293, baseEnd_2030293] using wordTrace_append hprefix tailTrace_2030293
  have hstable : (prefixWord ++ tailWord_2030293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030293).length < 2 ^ (prefixWord ++ tailWord_2030293).sum := by decide
  have hdescent : baseEnd_2030293 < baseStart_2030293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030308 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_2030308 : Nat := 118140960795 + 2030308 * 2 ^ 59
def prefixEnd_2030308 : Nat := 4983230072969 + 3 ^ 40 * 2030308 * 2
def baseEnd_2030308 : Nat := 695015920445831762875193

theorem tailTrace_2030308 : CollatzResearch.WordTrace tailWord_2030308 prefixEnd_2030308 695015920445831762875193 := by
  unfold tailWord_2030308
  simp only [CollatzResearch.WordTrace]
  refine ⟨37025708164274169922705789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49367610885698893230274385 37025708164274169922705789)
  ·
    refine ⟨13884640561602813721014671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37025708164274169922705789 13884640561602813721014671)
    ·
      refine ⟨20826960842404220581522007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13884640561602813721014671 20826960842404220581522007)
      ·
        refine ⟨31240441263606330872283011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20826960842404220581522007 31240441263606330872283011)
        ·
          refine ⟨46860661895409496308424517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31240441263606330872283011 46860661895409496308424517)
          ·
            refine ⟨8786374105389280557829597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46860661895409496308424517 8786374105389280557829597)
            ·
              refine ⟨3294890289520980209186099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8786374105389280557829597 3294890289520980209186099)
              ·
                refine ⟨4942335434281470313779149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3294890289520980209186099 4942335434281470313779149)
                ·
                  refine ⟨1853375787855551367667181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4942335434281470313779149 1853375787855551367667181)
                  ·
                    refine ⟨695015920445831762875193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1853375787855551367667181 695015920445831762875193)
                    ·
                      rfl

theorem cell22_2030308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_2030308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030308 prefixEnd_2030308 := by exact prefixLift 2030308
  have htrace : WordTrace (prefixWord ++ tailWord_2030308) baseStart_2030308 baseEnd_2030308 := by
    simpa [prefixWord, tailWord_2030308, baseEnd_2030308] using wordTrace_append hprefix tailTrace_2030308
  have hstable : (prefixWord ++ tailWord_2030308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030308).length < 2 ^ (prefixWord ++ tailWord_2030308).sum := by decide
  have hdescent : baseEnd_2030308 < baseStart_2030308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030321 : List Nat := [1, 2, 2, 2, 2, 2, 3, 3, 5]
def baseStart_2030321 : Nat := 118140960795 + 2030321 * 2 ^ 59
def prefixEnd_2030321 : Nat := 4983230072969 + 3 ^ 40 * 2030321 * 2
def baseEnd_2030321 : Nat := 231673456870501354100051

theorem tailTrace_2030321 : CollatzResearch.WordTrace tailWord_2030321 prefixEnd_2030321 231673456870501354100051 := by
  unfold tailWord_2030321
  simp only [CollatzResearch.WordTrace]
  refine ⟨74051890477501243065634817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49367926985000828710423211 74051890477501243065634817)
  ·
    refine ⟨55538917858125932299226113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74051890477501243065634817 55538917858125932299226113)
    ·
      refine ⟨41654188393594449224419585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55538917858125932299226113 41654188393594449224419585)
      ·
        refine ⟨31240641295195836918314689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41654188393594449224419585 31240641295195836918314689)
        ·
          refine ⟨23430480971396877688736017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31240641295195836918314689 23430480971396877688736017)
          ·
            refine ⟨17572860728547658266552013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23430480971396877688736017 17572860728547658266552013)
            ·
              refine ⟨6589822773205371849957005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17572860728547658266552013 6589822773205371849957005)
              ·
                refine ⟨2471183539952014443733877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6589822773205371849957005 2471183539952014443733877)
                ·
                  refine ⟨231673456870501354100051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2471183539952014443733877 231673456870501354100051)
                  ·
                    rfl

theorem cell22_2030321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 5].length) (baseStart_2030321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030321 prefixEnd_2030321 := by exact prefixLift 2030321
  have htrace : WordTrace (prefixWord ++ tailWord_2030321) baseStart_2030321 baseEnd_2030321 := by
    simpa [prefixWord, tailWord_2030321, baseEnd_2030321] using wordTrace_append hprefix tailTrace_2030321
  have hstable : (prefixWord ++ tailWord_2030321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030321).length < 2 ^ (prefixWord ++ tailWord_2030321).sum := by decide
  have hdescent : baseEnd_2030321 < baseStart_2030321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030359 : List Nat := [1, 1, 3, 4, 3, 2, 2, 2, 1, 3]
def baseStart_2030359 : Nat := 118140960795 + 2030359 * 2 ^ 59
def prefixEnd_2030359 : Nat := 4983230072969 + 3 ^ 40 * 2030359 * 2
def baseEnd_2030359 : Nat := 695033378788084629850037

theorem tailTrace_2030359 : CollatzResearch.WordTrace tailWord_2030359 prefixEnd_2030359 695033378788084629850037 := by
  unfold tailWord_2030359
  simp only [CollatzResearch.WordTrace]
  refine ⟨74053276451363575555518131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49368850967575717037012087 74053276451363575555518131)
  ·
    refine ⟨111079914677045363333277197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74053276451363575555518131 111079914677045363333277197)
    ·
      refine ⟨41654968003892011249978949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111079914677045363333277197 41654968003892011249978949)
      ·
        refine ⟨7810306500729752109371053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41654968003892011249978949 7810306500729752109371053)
        ·
          refine ⟨2928864937773657041014145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7810306500729752109371053 2928864937773657041014145)
          ·
            refine ⟨2196648703330242780760609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2928864937773657041014145 2196648703330242780760609)
            ·
              refine ⟨1647486527497682085570457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2196648703330242780760609 1647486527497682085570457)
              ·
                refine ⟨1235614895623261564177843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647486527497682085570457 1235614895623261564177843)
                ·
                  refine ⟨1853422343434892346266765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235614895623261564177843 1853422343434892346266765)
                  ·
                    refine ⟨695033378788084629850037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1853422343434892346266765 695033378788084629850037)
                    ·
                      rfl

theorem cell22_2030359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_2030359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030359 prefixEnd_2030359 := by exact prefixLift 2030359
  have htrace : WordTrace (prefixWord ++ tailWord_2030359) baseStart_2030359 baseEnd_2030359 := by
    simpa [prefixWord, tailWord_2030359, baseEnd_2030359] using wordTrace_append hprefix tailTrace_2030359
  have hstable : (prefixWord ++ tailWord_2030359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030359).length < 2 ^ (prefixWord ++ tailWord_2030359).sum := by decide
  have hdescent : baseEnd_2030359 < baseStart_2030359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030443 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 3, 3]
def baseStart_2030443 : Nat := 118140960795 + 2030443 * 2 ^ 59
def prefixEnd_2030443 : Nat := 4983230072969 + 3 ^ 40 * 2030443 * 2
def baseEnd_2030443 : Nat := 695062133704736410749779

theorem tailTrace_2030443 : CollatzResearch.WordTrace tailWord_2030443 prefixEnd_2030443 695062133704736410749779 := by
  unfold tailWord_2030443
  simp only [CollatzResearch.WordTrace]
  refine ⟨74056340183059257901575983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49370893455372838601050655 74056340183059257901575983)
  ·
    refine ⟨111084510274588886852363975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74056340183059257901575983 111084510274588886852363975)
    ·
      refine ⟨166626765411883330278545963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111084510274588886852363975 166626765411883330278545963)
      ·
        refine ⟨249940148117824995417818945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166626765411883330278545963 249940148117824995417818945)
        ·
          refine ⟨187455111088368746563364209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249940148117824995417818945 187455111088368746563364209)
          ·
            refine ⟨140591333316276559922523157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187455111088368746563364209 140591333316276559922523157)
            ·
              refine ⟨6590218749200463746368273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140591333316276559922523157 6590218749200463746368273)
              ·
                refine ⟨4942664061900347809776205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6590218749200463746368273 4942664061900347809776205)
                ·
                  refine ⟨1853499023212630428666077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4942664061900347809776205 1853499023212630428666077)
                  ·
                    refine ⟨695062133704736410749779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1853499023212630428666077 695062133704736410749779)
                    ·
                      rfl

theorem cell22_2030443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 3].length) (baseStart_2030443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030443 prefixEnd_2030443 := by exact prefixLift 2030443
  have htrace : WordTrace (prefixWord ++ tailWord_2030443) baseStart_2030443 baseEnd_2030443 := by
    simpa [prefixWord, tailWord_2030443, baseEnd_2030443] using wordTrace_append hprefix tailTrace_2030443
  have hstable : (prefixWord ++ tailWord_2030443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030443).length < 2 ^ (prefixWord ++ tailWord_2030443).sum := by decide
  have hdescent : baseEnd_2030443 < baseStart_2030443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030462 : List Nat := [4, 2, 3, 1, 3, 1, 8]
def baseStart_2030462 : Nat := 118140960795 + 2030462 * 2 ^ 59
def prefixEnd_2030462 : Nat := 4983230072969 + 3 ^ 40 * 2030462 * 2
def baseEnd_2030462 : Nat := 25743282881223210908323

theorem tailTrace_2030462 : CollatzResearch.WordTrace tailWord_2030462 prefixEnd_2030462 25743282881223210908323 := by
  unfold tailWord_2030462
  simp only [CollatzResearch.WordTrace]
  refine ⟨9257129146248803018314705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49371355446660282764345093 9257129146248803018314705)
  ·
    refine ⟨6942846859686602263736029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9257129146248803018314705 6942846859686602263736029)
    ·
      refine ⟨2603567572382475848901011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6942846859686602263736029 2603567572382475848901011)
      ·
        refine ⟨3905351358573713773351517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603567572382475848901011 3905351358573713773351517)
        ·
          refine ⟨1464506759465142665006819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3905351358573713773351517 1464506759465142665006819)
          ·
            refine ⟨2196760139197713997510229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464506759465142665006819 2196760139197713997510229)
            ·
              refine ⟨25743282881223210908323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2196760139197713997510229 25743282881223210908323)
              ·
                rfl

theorem cell22_2030462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 8].length) (baseStart_2030462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030462 prefixEnd_2030462 := by exact prefixLift 2030462
  have htrace : WordTrace (prefixWord ++ tailWord_2030462) baseStart_2030462 baseEnd_2030462 := by
    simpa [prefixWord, tailWord_2030462, baseEnd_2030462] using wordTrace_append hprefix tailTrace_2030462
  have hstable : (prefixWord ++ tailWord_2030462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030462).length < 2 ^ (prefixWord ++ tailWord_2030462).sum := by decide
  have hdescent : baseEnd_2030462 < baseStart_2030462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030490 : List Nat := [3, 1, 1, 4, 3, 1, 1, 3, 5]
def baseStart_2030490 : Nat := 118140960795 + 2030490 * 2 ^ 59
def prefixEnd_2030490 : Nat := 4983230072969 + 3 ^ 40 * 2030490 * 2
def baseEnd_2030490 : Nat := 231692740921747984941545

theorem tailTrace_2030490 : CollatzResearch.WordTrace tailWord_2030490 prefixEnd_2030490 231692740921747984941545 := by
  unfold tailWord_2030490
  simp only [CollatzResearch.WordTrace]
  refine ⟨18514513603472246232134231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49372036275925989952357949 18514513603472246232134231)
  ·
    refine ⟨27771770405208369348201347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18514513603472246232134231 27771770405208369348201347)
    ·
      refine ⟨41657655607812554022302021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27771770405208369348201347 41657655607812554022302021)
      ·
        refine ⟨7810810426464853879181629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41657655607812554022302021 7810810426464853879181629)
        ·
          refine ⟨2929053909924320204693111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7810810426464853879181629 2929053909924320204693111)
          ·
            refine ⟨4393580864886480307039667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2929053909924320204693111 4393580864886480307039667)
            ·
              refine ⟨6590371297329720460559501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4393580864886480307039667 6590371297329720460559501)
              ·
                refine ⟨2471389236498645172709813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6590371297329720460559501 2471389236498645172709813)
                ·
                  refine ⟨231692740921747984941545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2471389236498645172709813 231692740921747984941545)
                  ·
                    rfl

theorem cell22_2030490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_2030490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030490 prefixEnd_2030490 := by exact prefixLift 2030490
  have htrace : WordTrace (prefixWord ++ tailWord_2030490) baseStart_2030490 baseEnd_2030490 := by
    simpa [prefixWord, tailWord_2030490, baseEnd_2030490] using wordTrace_append hprefix tailTrace_2030490
  have hstable : (prefixWord ++ tailWord_2030490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030490).length < 2 ^ (prefixWord ++ tailWord_2030490).sum := by decide
  have hdescent : baseEnd_2030490 < baseStart_2030490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030533 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 8, 3]
def baseStart_2030533 : Nat := 118140960795 + 2030533 * 2 ^ 59
def prefixEnd_2030533 : Nat := 4983230072969 + 3 ^ 40 * 2030533 * 2
def baseEnd_2030533 : Nat := 695092942544006175999503

theorem tailTrace_2030533 : CollatzResearch.WordTrace tailWord_2030533 prefixEnd_2030533 695092942544006175999503 := by
  unfold tailWord_2030533
  simp only [CollatzResearch.WordTrace]
  refine ⟨74059622752733203272352253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49373081835155468848234835 74059622752733203272352253)
  ·
    refine ⟨27772358532274951227132095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74059622752733203272352253 27772358532274951227132095)
    ·
      refine ⟨41658537798412426840698143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27772358532274951227132095 41658537798412426840698143)
      ·
        refine ⟨62487806697618640261047215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41658537798412426840698143 62487806697618640261047215)
        ·
          refine ⟨93731710046427960391570823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62487806697618640261047215 93731710046427960391570823)
          ·
            refine ⟨140597565069641940587356235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93731710046427960391570823 140597565069641940587356235)
            ·
              refine ⟨210896347604462910881034353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140597565069641940587356235 210896347604462910881034353)
              ·
                refine ⟨158172260703347183160775765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210896347604462910881034353 158172260703347183160775765)
                ·
                  refine ⟨1853581180117349802665341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 158172260703347183160775765 1853581180117349802665341)
                  ·
                    refine ⟨695092942544006175999503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1853581180117349802665341 695092942544006175999503)
                    ·
                      rfl

theorem cell22_2030533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_2030533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030533 prefixEnd_2030533 := by exact prefixLift 2030533
  have htrace : WordTrace (prefixWord ++ tailWord_2030533) baseStart_2030533 baseEnd_2030533 := by
    simpa [prefixWord, tailWord_2030533, baseEnd_2030533] using wordTrace_append hprefix tailTrace_2030533
  have hstable : (prefixWord ++ tailWord_2030533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030533).length < 2 ^ (prefixWord ++ tailWord_2030533).sum := by decide
  have hdescent : baseEnd_2030533 < baseStart_2030533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030700 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_2030700 : Nat := 118140960795 + 2030700 * 2 ^ 59
def prefixEnd_2030700 : Nat := 4983230072969 + 3 ^ 40 * 2030700 * 2
def baseEnd_2030700 : Nat := 695150110056873407073991

theorem tailTrace_2030700 : CollatzResearch.WordTrace tailWord_2030700 prefixEnd_2030700 695150110056873407073991 := by
  unfold tailWord_2030700
  simp only [CollatzResearch.WordTrace]
  refine ⟨37032856871564095396840777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49377142495418793862454369 37032856871564095396840777)
  ·
    refine ⟨27774642653673071547630583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37032856871564095396840777 27774642653673071547630583)
    ·
      refine ⟨41661963980509607321445875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27774642653673071547630583 41661963980509607321445875)
      ·
        refine ⟨62492945970764410982168813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41661963980509607321445875 62492945970764410982168813)
        ·
          refine ⟨23434854739036654118313305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62492945970764410982168813 23434854739036654118313305)
          ·
            refine ⟨17576141054277490588734979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23434854739036654118313305 17576141054277490588734979)
            ·
              refine ⟨26364211581416235883102469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17576141054277490588734979 26364211581416235883102469)
              ·
                refine ⟨4943289671515544228081713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26364211581416235883102469 4943289671515544228081713)
                ·
                  refine ⟨3707467253636658171061285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4943289671515544228081713 3707467253636658171061285)
                  ·
                    refine ⟨695150110056873407073991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3707467253636658171061285 695150110056873407073991)
                    ·
                      rfl

theorem cell22_2030700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_2030700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030700 prefixEnd_2030700 := by exact prefixLift 2030700
  have htrace : WordTrace (prefixWord ++ tailWord_2030700) baseStart_2030700 baseEnd_2030700 := by
    simpa [prefixWord, tailWord_2030700, baseEnd_2030700] using wordTrace_append hprefix tailTrace_2030700
  have hstable : (prefixWord ++ tailWord_2030700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030700).length < 2 ^ (prefixWord ++ tailWord_2030700).sum := by decide
  have hdescent : baseEnd_2030700 < baseStart_2030700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030734 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_2030734 : Nat := 118140960795 + 2030734 * 2 ^ 59
def prefixEnd_2030734 : Nat := 4983230072969 + 3 ^ 40 * 2030734 * 2
def baseEnd_2030734 : Nat := 695161748951708651723887

theorem tailTrace_2030734 : CollatzResearch.WordTrace tailWord_2030734 prefixEnd_2030734 695161748951708651723887 := by
  unfold tailWord_2030734
  simp only [CollatzResearch.WordTrace]
  refine ⟨9258369228125626825052407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49377969216670009733612837 9258369228125626825052407)
  ·
    refine ⟨13887553842188440237578611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9258369228125626825052407 13887553842188440237578611)
    ·
      refine ⟨20831330763282660356367917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13887553842188440237578611 20831330763282660356367917)
      ·
        refine ⟨7811749036230997633637969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20831330763282660356367917 7811749036230997633637969)
        ·
          refine ⟨5858811777173248225228477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7811749036230997633637969 5858811777173248225228477)
          ·
            refine ⟨2197054416439968084460679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5858811777173248225228477 2197054416439968084460679)
            ·
              refine ⟨3295581624659952126691019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197054416439968084460679 3295581624659952126691019)
              ·
                refine ⟨4943372436989928190036529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3295581624659952126691019 4943372436989928190036529)
                ·
                  refine ⟨3707529327742446142527397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4943372436989928190036529 3707529327742446142527397)
                  ·
                    refine ⟨695161748951708651723887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3707529327742446142527397 695161748951708651723887)
                    ·
                      rfl

theorem cell22_2030734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_2030734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030734 prefixEnd_2030734 := by exact prefixLift 2030734
  have htrace : WordTrace (prefixWord ++ tailWord_2030734) baseStart_2030734 baseEnd_2030734 := by
    simpa [prefixWord, tailWord_2030734, baseEnd_2030734] using wordTrace_append hprefix tailTrace_2030734
  have hstable : (prefixWord ++ tailWord_2030734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030734).length < 2 ^ (prefixWord ++ tailWord_2030734).sum := by decide
  have hdescent : baseEnd_2030734 < baseStart_2030734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030775 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 2, 5]
def baseStart_2030775 : Nat := 118140960795 + 2030775 * 2 ^ 59
def prefixEnd_2030775 : Nat := 4983230072969 + 3 ^ 40 * 2030775 * 2
def baseEnd_2030775 : Nat := 695175784089598211448761

theorem tailTrace_2030775 : CollatzResearch.WordTrace tailWord_2030775 prefixEnd_2030775 695175784089598211448761 := by
  unfold tailWord_2030775
  simp only [CollatzResearch.WordTrace]
  refine ⟨74068449217856478602661779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49378966145237652401774519 74068449217856478602661779)
  ·
    refine ⟨111102673826784717903992669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74068449217856478602661779 111102673826784717903992669)
    ·
      refine ⟨41663502685044269213997251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111102673826784717903992669 41663502685044269213997251)
      ·
        refine ⟨62495254027566403820995877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41663502685044269213997251 62495254027566403820995877)
        ·
          refine ⟨11717860130168700716436727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62495254027566403820995877 11717860130168700716436727)
          ·
            refine ⟨17576790195253051074655091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11717860130168700716436727 17576790195253051074655091)
            ·
              refine ⟨26365185292879576611982637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17576790195253051074655091 26365185292879576611982637)
              ·
                refine ⟨9886944484829841229493489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26365185292879576611982637 9886944484829841229493489)
                ·
                  refine ⟨7415208363622380922120117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9886944484829841229493489 7415208363622380922120117)
                  ·
                    refine ⟨695175784089598211448761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7415208363622380922120117 695175784089598211448761)
                    ·
                      rfl

theorem cell22_2030775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_2030775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030775 prefixEnd_2030775 := by exact prefixLift 2030775
  have htrace : WordTrace (prefixWord ++ tailWord_2030775) baseStart_2030775 baseEnd_2030775 := by
    simpa [prefixWord, tailWord_2030775, baseEnd_2030775] using wordTrace_append hprefix tailTrace_2030775
  have hstable : (prefixWord ++ tailWord_2030775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030775).length < 2 ^ (prefixWord ++ tailWord_2030775).sum := by decide
  have hdescent : baseEnd_2030775 < baseStart_2030775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030798 : List Nat := [4, 1, 1, 1, 5, 2, 1, 3, 1, 3]
def baseStart_2030798 : Nat := 118140960795 + 2030798 * 2 ^ 59
def prefixEnd_2030798 : Nat := 4983230072969 + 3 ^ 40 * 2030798 * 2
def baseEnd_2030798 : Nat := 695183657459633818123691

theorem tailTrace_2030798 : CollatzResearch.WordTrace tailWord_2030798 prefixEnd_2030798 695183657459633818123691 := by
  unfold tailWord_2030798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9258661012096644191343631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49379525397848769020499365 9258661012096644191343631)
  ·
    refine ⟨13887991518144966287015447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9258661012096644191343631 13887991518144966287015447)
    ·
      refine ⟨20831987277217449430523171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13887991518144966287015447 20831987277217449430523171)
      ·
        refine ⟨31247980915826174145784757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20831987277217449430523171 31247980915826174145784757)
        ·
          refine ⟨2929498210858703826167321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31247980915826174145784757 2929498210858703826167321)
          ·
            refine ⟨2197123658144027869625491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2929498210858703826167321 2197123658144027869625491)
            ·
              refine ⟨3295685487216041804438237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197123658144027869625491 3295685487216041804438237)
              ·
                refine ⟨1235882057706015676664339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3295685487216041804438237 1235882057706015676664339)
                ·
                  refine ⟨1853823086559023514996509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235882057706015676664339 1853823086559023514996509)
                  ·
                    refine ⟨695183657459633818123691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1853823086559023514996509 695183657459633818123691)
                    ·
                      rfl

theorem cell22_2030798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_2030798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030798 prefixEnd_2030798 := by exact prefixLift 2030798
  have htrace : WordTrace (prefixWord ++ tailWord_2030798) baseStart_2030798 baseEnd_2030798 := by
    simpa [prefixWord, tailWord_2030798, baseEnd_2030798] using wordTrace_append hprefix tailTrace_2030798
  have hstable : (prefixWord ++ tailWord_2030798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030798).length < 2 ^ (prefixWord ++ tailWord_2030798).sum := by decide
  have hdescent : baseEnd_2030798 < baseStart_2030798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030807 : List Nat := [1, 1, 3, 2, 1, 2, 4, 3, 1, 4]
def baseStart_2030807 : Nat := 118140960795 + 2030807 * 2 ^ 59
def prefixEnd_2030807 : Nat := 4983230072969 + 3 ^ 40 * 2030807 * 2
def baseEnd_2030807 : Nat := 695186738343560794648663

theorem tailTrace_2030807 : CollatzResearch.WordTrace tailWord_2030807 prefixEnd_2030807 695186738343560794648663 := by
  unfold tailWord_2030807
  simp only [CollatzResearch.WordTrace]
  refine ⟨74069616353740548067826675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49379744235827032045217783 74069616353740548067826675)
  ·
    refine ⟨111104424530610822101740013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74069616353740548067826675 111104424530610822101740013)
    ·
      refine ⟨41664159198979058288152505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111104424530610822101740013 41664159198979058288152505)
      ·
        refine ⟨31248119399234293716114379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41664159198979058288152505 31248119399234293716114379)
        ·
          refine ⟨46872179098851440574171569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31248119399234293716114379 46872179098851440574171569)
          ·
            refine ⟨35154134324138580430628677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46872179098851440574171569 35154134324138580430628677)
            ·
              refine ⟨6591400185775983830742877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35154134324138580430628677 6591400185775983830742877)
              ·
                refine ⟨2471775069665993936528579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6591400185775983830742877 2471775069665993936528579)
                ·
                  refine ⟨3707662604498990904792869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471775069665993936528579 3707662604498990904792869)
                  ·
                    refine ⟨695186738343560794648663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3707662604498990904792869 695186738343560794648663)
                    ·
                      rfl

theorem cell22_2030807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_2030807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030807 prefixEnd_2030807 := by exact prefixLift 2030807
  have htrace : WordTrace (prefixWord ++ tailWord_2030807) baseStart_2030807 baseEnd_2030807 := by
    simpa [prefixWord, tailWord_2030807, baseEnd_2030807] using wordTrace_append hprefix tailTrace_2030807
  have hstable : (prefixWord ++ tailWord_2030807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030807).length < 2 ^ (prefixWord ++ tailWord_2030807).sum := by decide
  have hdescent : baseEnd_2030807 < baseStart_2030807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030895 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 9]
def baseStart_2030895 : Nat := 118140960795 + 2030895 * 2 ^ 59
def prefixEnd_2030895 : Nat := 4983230072969 + 3 ^ 40 * 2030895 * 2
def baseEnd_2030895 : Nat := 231738954180652632816131

theorem tailTrace_2030895 : CollatzResearch.WordTrace tailWord_2030895 prefixEnd_2030895 231738954180652632816131 := by
  unfold tailWord_2030895
  simp only [CollatzResearch.WordTrace]
  refine ⟨74072825977421739097030139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49381883984947826064686759 74072825977421739097030139)
  ·
    refine ⟨111109238966132608645545209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74072825977421739097030139 111109238966132608645545209)
    ·
      refine ⟨83331929224599456484158907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111109238966132608645545209 83331929224599456484158907)
      ·
        refine ⟨124997893836899184726238361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83331929224599456484158907 124997893836899184726238361)
        ·
          refine ⟨93748420377674388544678771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124997893836899184726238361 93748420377674388544678771)
          ·
            refine ⟨140622630566511582817018157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93748420377674388544678771 140622630566511582817018157)
            ·
              refine ⟨52733486462441843556381809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140622630566511582817018157 52733486462441843556381809)
              ·
                refine ⟨39550114846831382667286357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52733486462441843556381809 39550114846831382667286357)
                ·
                  refine ⟨231738954180652632816131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39550114846831382667286357 231738954180652632816131)
                  ·
                    rfl

theorem cell22_2030895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 9].length) (baseStart_2030895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030895 prefixEnd_2030895 := by exact prefixLift 2030895
  have htrace : WordTrace (prefixWord ++ tailWord_2030895) baseStart_2030895 baseEnd_2030895 := by
    simpa [prefixWord, tailWord_2030895, baseEnd_2030895] using wordTrace_append hprefix tailTrace_2030895
  have hstable : (prefixWord ++ tailWord_2030895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030895).length < 2 ^ (prefixWord ++ tailWord_2030895).sum := by decide
  have hdescent : baseEnd_2030895 < baseStart_2030895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030899 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 3, 3]
def baseStart_2030899 : Nat := 118140960795 + 2030899 * 2 ^ 59
def prefixEnd_2030899 : Nat := 4983230072969 + 3 ^ 40 * 2030899 * 2
def baseEnd_2030899 : Nat := 695218231823703221348381

theorem tailTrace_2030899 : CollatzResearch.WordTrace tailWord_2030899 prefixEnd_2030899 695218231823703221348381 := by
  unfold tailWord_2030899
  simp only [CollatzResearch.WordTrace]
  refine ⟨74072971869407247780175751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49381981246271498520117167 74072971869407247780175751)
  ·
    refine ⟨111109457804110871670263627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74072971869407247780175751 111109457804110871670263627)
    ·
      refine ⟨166664186706166307505395441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111109457804110871670263627 166664186706166307505395441)
      ·
        refine ⟨124998140029624730629046581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166664186706166307505395441 124998140029624730629046581)
        ·
          refine ⟨11718575627777318496473117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124998140029624730629046581 11718575627777318496473117)
          ·
            refine ⟨4394465860416494436177419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11718575627777318496473117 4394465860416494436177419)
            ·
              refine ⟨6591698790624741654266129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4394465860416494436177419 6591698790624741654266129)
              ·
                refine ⟨4943774092968556240699597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6591698790624741654266129 4943774092968556240699597)
                ·
                  refine ⟨1853915284863208590262349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4943774092968556240699597 1853915284863208590262349)
                  ·
                    refine ⟨695218231823703221348381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1853915284863208590262349 695218231823703221348381)
                    ·
                      rfl

theorem cell22_2030899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 3].length) (baseStart_2030899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030899 prefixEnd_2030899 := by exact prefixLift 2030899
  have htrace : WordTrace (prefixWord ++ tailWord_2030899) baseStart_2030899 baseEnd_2030899 := by
    simpa [prefixWord, tailWord_2030899, baseEnd_2030899] using wordTrace_append hprefix tailTrace_2030899
  have hstable : (prefixWord ++ tailWord_2030899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030899).length < 2 ^ (prefixWord ++ tailWord_2030899).sum := by decide
  have hdescent : baseEnd_2030899 < baseStart_2030899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030946 : List Nat := [3, 3, 2, 1, 1, 1, 5, 1, 5]
def baseStart_2030946 : Nat := 118140960795 + 2030946 * 2 ^ 59
def prefixEnd_2030946 : Nat := 4983230072969 + 3 ^ 40 * 2030946 * 2
def baseEnd_2030946 : Nat := 231744773628070255141079

theorem tailTrace_2030946 : CollatzResearch.WordTrace tailWord_2030946 prefixEnd_2030946 231744773628070255141079 := by
  unfold tailWord_2030946
  simp only [CollatzResearch.WordTrace]
  refine ⟨18518671525059243701784173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49383124066824649871424461 18518671525059243701784173)
  ·
    refine ⟨6944501821897216388169065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18518671525059243701784173 6944501821897216388169065)
    ·
      refine ⟨5208376366422912291126799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6944501821897216388169065 5208376366422912291126799)
      ·
        refine ⟨7812564549634368436690199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5208376366422912291126799 7812564549634368436690199)
        ·
          refine ⟨11718846824451552655035299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7812564549634368436690199 11718846824451552655035299)
          ·
            refine ⟨17578270236677328982552949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11718846824451552655035299 17578270236677328982552949)
            ·
              refine ⟨1647962834688499592114339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17578270236677328982552949 1647962834688499592114339)
              ·
                refine ⟨2471944252032749388171509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647962834688499592114339 2471944252032749388171509)
                ·
                  refine ⟨231744773628070255141079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2471944252032749388171509 231744773628070255141079)
                  ·
                    rfl

theorem cell22_2030946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_2030946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030946 prefixEnd_2030946 := by exact prefixLift 2030946
  have htrace : WordTrace (prefixWord ++ tailWord_2030946) baseStart_2030946 baseEnd_2030946 := by
    simpa [prefixWord, tailWord_2030946, baseEnd_2030946] using wordTrace_append hprefix tailTrace_2030946
  have hstable : (prefixWord ++ tailWord_2030946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030946).length < 2 ^ (prefixWord ++ tailWord_2030946).sum := by decide
  have hdescent : baseEnd_2030946 < baseStart_2030946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030959 : List Nat := [1, 1, 2, 1, 3, 1, 6, 2, 1, 4]
def baseStart_2030959 : Nat := 118140960795 + 2030959 * 2 ^ 59
def prefixEnd_2030959 : Nat := 4983230072969 + 3 ^ 40 * 2030959 * 2
def baseEnd_2030959 : Nat := 695238771049883064848197

theorem tailTrace_2030959 : CollatzResearch.WordTrace tailWord_2030959 prefixEnd_2030959 695238771049883064848197 := by
  unfold tailWord_2030959
  simp only [CollatzResearch.WordTrace]
  refine ⟨74075160249189878027359931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49383440166126585351573287 74075160249189878027359931)
  ·
    refine ⟨111112740373784817041039897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74075160249189878027359931 111112740373784817041039897)
    ·
      refine ⟨83334555280338612780779923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111112740373784817041039897 83334555280338612780779923)
      ·
        refine ⟨125001832920507919171169885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83334555280338612780779923 125001832920507919171169885)
        ·
          refine ⟨46875687345190469689188707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125001832920507919171169885 46875687345190469689188707)
          ·
            refine ⟨70313531017785704533783061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46875687345190469689188707 70313531017785704533783061)
            ·
              refine ⟨3295946766458704900021081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70313531017785704533783061 3295946766458704900021081)
              ·
                refine ⟨2471960074844028675015811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3295946766458704900021081 2471960074844028675015811)
                ·
                  refine ⟨3707940112266043012523717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471960074844028675015811 3707940112266043012523717)
                  ·
                    refine ⟨695238771049883064848197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3707940112266043012523717 695238771049883064848197)
                    ·
                      rfl

theorem cell22_2030959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_2030959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030959 prefixEnd_2030959 := by exact prefixLift 2030959
  have htrace : WordTrace (prefixWord ++ tailWord_2030959) baseStart_2030959 baseEnd_2030959 := by
    simpa [prefixWord, tailWord_2030959, baseEnd_2030959] using wordTrace_append hprefix tailTrace_2030959
  have hstable : (prefixWord ++ tailWord_2030959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030959).length < 2 ^ (prefixWord ++ tailWord_2030959).sum := by decide
  have hdescent : baseEnd_2030959 < baseStart_2030959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030972 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_2030972 : Nat := 118140960795 + 2030972 * 2 ^ 59
def prefixEnd_2030972 : Nat := 4983230072969 + 3 ^ 40 * 2030972 * 2
def baseEnd_2030972 : Nat := 695243221215555364273157

theorem tailTrace_2030972 : CollatzResearch.WordTrace tailWord_2030972 prefixEnd_2030972 695243221215555364273157 := by
  unfold tailWord_2030972
  simp only [CollatzResearch.WordTrace]
  refine ⟨37037817199071390623791585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49383756265428520831722113 37037817199071390623791585)
  ·
    refine ⟨27778362899303542967843689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37037817199071390623791585 27778362899303542967843689)
    ·
      refine ⟨20833772174477657225882767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27778362899303542967843689 20833772174477657225882767)
      ·
        refine ⟨31250658261716485838824151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20833772174477657225882767 31250658261716485838824151)
        ·
          refine ⟨46875987392574728758236227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31250658261716485838824151 46875987392574728758236227)
          ·
            refine ⟨70313981088862093137354341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46875987392574728758236227 70313981088862093137354341)
            ·
              refine ⟨13183871454161642463253939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70313981088862093137354341 13183871454161642463253939)
              ·
                refine ⟨19775807181242463694880909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13183871454161642463253939 19775807181242463694880909)
                ·
                  refine ⟨7415927692965923885580341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19775807181242463694880909 7415927692965923885580341)
                  ·
                    refine ⟨695243221215555364273157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7415927692965923885580341 695243221215555364273157)
                    ·
                      rfl

theorem cell22_2030972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_2030972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2030972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2030972 prefixEnd_2030972 := by exact prefixLift 2030972
  have htrace : WordTrace (prefixWord ++ tailWord_2030972) baseStart_2030972 baseEnd_2030972 := by
    simpa [prefixWord, tailWord_2030972, baseEnd_2030972] using wordTrace_append hprefix tailTrace_2030972
  have hstable : (prefixWord ++ tailWord_2030972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030972).length < 2 ^ (prefixWord ++ tailWord_2030972).sum := by decide
  have hdescent : baseEnd_2030972 < baseStart_2030972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031021 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2031021 : Nat := 118140960795 + 2031021 * 2 ^ 59
def prefixEnd_2031021 : Nat := 4983230072969 + 3 ^ 40 * 2031021 * 2
def baseEnd_2031021 : Nat := 695259994916935569798007

theorem tailTrace_2031021 : CollatzResearch.WordTrace tailWord_2031021 prefixEnd_2031021 695259994916935569798007 := by
  unfold tailWord_2031021
  simp only [CollatzResearch.WordTrace]
  refine ⟨74077421574965262616116917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49384947716643508410744611 74077421574965262616116917)
  ·
    refine ⟨6944758272652993370260961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74077421574965262616116917 6944758272652993370260961)
    ·
      refine ⟨5208568704489745027695721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6944758272652993370260961 5208568704489745027695721)
      ·
        refine ⟨3906426528367308770771791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5208568704489745027695721 3906426528367308770771791)
        ·
          refine ⟨5859639792550963156157687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3906426528367308770771791 5859639792550963156157687)
          ·
            refine ⟨8789459688826444734236531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5859639792550963156157687 8789459688826444734236531)
            ·
              refine ⟨13184189533239667101354797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8789459688826444734236531 13184189533239667101354797)
              ·
                refine ⟨4944071074964875163008049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13184189533239667101354797 4944071074964875163008049)
                ·
                  refine ⟨3708053306223656372256037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4944071074964875163008049 3708053306223656372256037)
                  ·
                    refine ⟨695259994916935569798007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3708053306223656372256037 695259994916935569798007)
                    ·
                      rfl

theorem cell22_2031021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2031021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031021 prefixEnd_2031021 := by exact prefixLift 2031021
  have htrace : WordTrace (prefixWord ++ tailWord_2031021) baseStart_2031021 baseEnd_2031021 := by
    simpa [prefixWord, tailWord_2031021, baseEnd_2031021] using wordTrace_append hprefix tailTrace_2031021
  have hstable : (prefixWord ++ tailWord_2031021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031021).length < 2 ^ (prefixWord ++ tailWord_2031021).sum := by decide
  have hdescent : baseEnd_2031021 < baseStart_2031021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031064 : List Nat := [2, 1, 2, 2, 2, 1, 4, 3, 5]
def baseStart_2031064 : Nat := 118140960795 + 2031064 * 2 ^ 59
def prefixEnd_2031064 : Nat := 4983230072969 + 3 ^ 40 * 2031064 * 2
def baseEnd_2031064 : Nat := 231758238231899263657625

theorem tailTrace_2031064 : CollatzResearch.WordTrace tailWord_2031064 prefixEnd_2031064 231758238231899263657625 := by
  unfold tailWord_2031064
  simp only [CollatzResearch.WordTrace]
  refine ⟨37039494956904740479966123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49385993275872987306621497 37039494956904740479966123)
  ·
    refine ⟨55559242435357110719949185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37039494956904740479966123 55559242435357110719949185)
    ·
      refine ⟨41669431826517833039961889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55559242435357110719949185 41669431826517833039961889)
      ·
        refine ⟨31252073869888374779971417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41669431826517833039961889 31252073869888374779971417)
        ·
          refine ⟨23439055402416281084978563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31252073869888374779971417 23439055402416281084978563)
          ·
            refine ⟨35158583103624421627467845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23439055402416281084978563 35158583103624421627467845)
            ·
              refine ⟨6592234331929579055150221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35158583103624421627467845 6592234331929579055150221)
              ·
                refine ⟨2472087874473592145681333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6592234331929579055150221 2472087874473592145681333)
                ·
                  refine ⟨231758238231899263657625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2472087874473592145681333 231758238231899263657625)
                  ·
                    rfl

theorem cell22_2031064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 5].length) (baseStart_2031064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031064 prefixEnd_2031064 := by exact prefixLift 2031064
  have htrace : WordTrace (prefixWord ++ tailWord_2031064) baseStart_2031064 baseEnd_2031064 := by
    simpa [prefixWord, tailWord_2031064, baseEnd_2031064] using wordTrace_append hprefix tailTrace_2031064
  have hstable : (prefixWord ++ tailWord_2031064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031064).length < 2 ^ (prefixWord ++ tailWord_2031064).sum := by decide
  have hdescent : baseEnd_2031064 < baseStart_2031064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031128 : List Nat := [2, 1, 2, 3, 4, 1, 2, 2, 1, 4]
def baseStart_2031128 : Nat := 118140960795 + 2031128 * 2 ^ 59
def prefixEnd_2031128 : Nat := 4983230072969 + 3 ^ 40 * 2031128 * 2
def baseEnd_2031128 : Nat := 695296623203622957372679

theorem tailTrace_2031128 : CollatzResearch.WordTrace tailWord_2031128 prefixEnd_2031128 695296623203622957372679 := by
  unfold tailWord_2031128
  simp only [CollatzResearch.WordTrace]
  refine ⟨37040662092788809945131019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49387549457051746593508025 37040662092788809945131019)
  ·
    refine ⟨55560993139183214917696529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37040662092788809945131019 55560993139183214917696529)
    ·
      refine ⟨41670744854387411188272397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55560993139183214917696529 41670744854387411188272397)
      ·
        refine ⟨15626529320395279195602149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41670744854387411188272397 15626529320395279195602149)
        ·
          refine ⟨2929974247574114849175403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15626529320395279195602149 2929974247574114849175403)
          ·
            refine ⟨4394961371361172273763105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2929974247574114849175403 4394961371361172273763105)
            ·
              refine ⟨3296221028520879205322329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4394961371361172273763105 3296221028520879205322329)
              ·
                refine ⟨2472165771390659403991747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3296221028520879205322329 2472165771390659403991747)
                ·
                  refine ⟨3708248657085989105987621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2472165771390659403991747 3708248657085989105987621)
                  ·
                    refine ⟨695296623203622957372679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3708248657085989105987621 695296623203622957372679)
                    ·
                      rfl

theorem cell22_2031128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_2031128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031128 prefixEnd_2031128 := by exact prefixLift 2031128
  have htrace : WordTrace (prefixWord ++ tailWord_2031128) baseStart_2031128 baseEnd_2031128 := by
    simpa [prefixWord, tailWord_2031128, baseEnd_2031128] using wordTrace_append hprefix tailTrace_2031128
  have hstable : (prefixWord ++ tailWord_2031128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031128).length < 2 ^ (prefixWord ++ tailWord_2031128).sum := by decide
  have hdescent : baseEnd_2031128 < baseStart_2031128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031216 : List Nat := [2, 1, 1, 1, 6, 1, 1, 4, 5]
def baseStart_2031216 : Nat := 118140960795 + 2031216 * 2 ^ 59
def prefixEnd_2031216 : Nat := 4983230072969 + 3 ^ 40 * 2031216 * 2
def baseEnd_2031216 : Nat := 231775582467340020390803

theorem tailTrace_2031216 : CollatzResearch.WordTrace tailWord_2031216 prefixEnd_2031216 231775582467340020390803 := by
  unfold tailWord_2031216
  simp only [CollatzResearch.WordTrace]
  refine ⟨37042266904629405459732751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49389689206172540612977001 37042266904629405459732751)
  ·
    refine ⟨55563400356944108189599127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37042266904629405459732751 55563400356944108189599127)
    ·
      refine ⟨83345100535416162284398691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55563400356944108189599127 83345100535416162284398691)
      ·
        refine ⟨125017650803124243426598037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83345100535416162284398691 125017650803124243426598037)
        ·
          refine ⟨5860202381396448910621783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125017650803124243426598037 5860202381396448910621783)
          ·
            refine ⟨8790303572094673365932675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860202381396448910621783 8790303572094673365932675)
            ·
              refine ⟨13185455358142010048899013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8790303572094673365932675 13185455358142010048899013)
              ·
                refine ⟨2472272879651626884168565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13185455358142010048899013 2472272879651626884168565)
                ·
                  refine ⟨231775582467340020390803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2472272879651626884168565 231775582467340020390803)
                  ·
                    rfl

theorem cell22_2031216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 5].length) (baseStart_2031216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031216 prefixEnd_2031216 := by exact prefixLift 2031216
  have htrace : WordTrace (prefixWord ++ tailWord_2031216) baseStart_2031216 baseEnd_2031216 := by
    simpa [prefixWord, tailWord_2031216, baseEnd_2031216] using wordTrace_append hprefix tailTrace_2031216
  have hstable : (prefixWord ++ tailWord_2031216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031216).length < 2 ^ (prefixWord ++ tailWord_2031216).sum := by decide
  have hdescent : baseEnd_2031216 < baseStart_2031216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031432 : List Nat := [2, 1, 3, 1, 1, 6, 2, 1, 1, 4]
def baseStart_2031432 : Nat := 118140960795 + 2031432 * 2 ^ 59
def prefixEnd_2031432 : Nat := 4983230072969 + 3 ^ 40 * 2031432 * 2
def baseEnd_2031432 : Nat := 695400688616267497771747

theorem tailTrace_2031432 : CollatzResearch.WordTrace tailWord_2031432 prefixEnd_2031432 695400688616267497771747 := by
  unfold tailWord_2031432
  simp only [CollatzResearch.WordTrace]
  refine ⟨37046205988238139904664275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49394941317650853206219033 37046205988238139904664275)
  ·
    refine ⟨55569308982357209856996413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37046205988238139904664275 55569308982357209856996413)
    ·
      refine ⟨20838490868383953696373655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55569308982357209856996413 20838490868383953696373655)
      ·
        refine ⟨31257736302575930544560483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20838490868383953696373655 31257736302575930544560483)
        ·
          refine ⟨46886604453863895816840725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31257736302575930544560483 46886604453863895816840725)
          ·
            refine ⟨2197809583774870116414409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46886604453863895816840725 2197809583774870116414409)
            ·
              refine ⟨1648357187831152587310807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2197809583774870116414409 1648357187831152587310807)
              ·
                refine ⟨2472535781746728880966211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1648357187831152587310807 2472535781746728880966211)
                ·
                  refine ⟨3708803672620093321449317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2472535781746728880966211 3708803672620093321449317)
                  ·
                    refine ⟨695400688616267497771747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3708803672620093321449317 695400688616267497771747)
                    ·
                      rfl

theorem cell22_2031432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_2031432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031432 prefixEnd_2031432 := by exact prefixLift 2031432
  have htrace : WordTrace (prefixWord ++ tailWord_2031432) baseStart_2031432 baseEnd_2031432 := by
    simpa [prefixWord, tailWord_2031432, baseEnd_2031432] using wordTrace_append hprefix tailTrace_2031432
  have hstable : (prefixWord ++ tailWord_2031432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031432).length < 2 ^ (prefixWord ++ tailWord_2031432).sum := by decide
  have hdescent : baseEnd_2031432 < baseStart_2031432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031445 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 4, 3]
def baseStart_2031445 : Nat := 118140960795 + 2031445 * 2 ^ 59
def prefixEnd_2031445 : Nat := 4983230072969 + 3 ^ 40 * 2031445 * 2
def baseEnd_2031445 : Nat := 695405138781939797196707

theorem tailTrace_2031445 : CollatzResearch.WordTrace tailWord_2031445 prefixEnd_2031445 695405138781939797196707 := by
  unfold tailWord_2031445
  simp only [CollatzResearch.WordTrace]
  refine ⟨74092886125429183029551789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49395257416952788686367859 74092886125429183029551789)
  ·
    refine ⟨27784832297035943636081921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74092886125429183029551789 27784832297035943636081921)
    ·
      refine ⟨20838624222776957727061441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27784832297035943636081921 20838624222776957727061441)
      ·
        refine ⟨15628968167082718295296081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20838624222776957727061441 15628968167082718295296081)
        ·
          refine ⟨11721726125312038721472061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15628968167082718295296081 11721726125312038721472061)
          ·
            refine ⟨4395647296992014520552023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11721726125312038721472061 4395647296992014520552023)
            ·
              refine ⟨6593470945488021780828035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4395647296992014520552023 6593470945488021780828035)
              ·
                refine ⟨9890206418232032671242053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593470945488021780828035 9890206418232032671242053)
                ·
                  refine ⟨1854413703418506125857885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9890206418232032671242053 1854413703418506125857885)
                  ·
                    refine ⟨695405138781939797196707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1854413703418506125857885 695405138781939797196707)
                    ·
                      rfl

theorem cell22_2031445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_2031445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031445 prefixEnd_2031445 := by exact prefixLift 2031445
  have htrace : WordTrace (prefixWord ++ tailWord_2031445) baseStart_2031445 baseEnd_2031445 := by
    simpa [prefixWord, tailWord_2031445, baseEnd_2031445] using wordTrace_append hprefix tailTrace_2031445
  have hstable : (prefixWord ++ tailWord_2031445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031445).length < 2 ^ (prefixWord ++ tailWord_2031445).sum := by decide
  have hdescent : baseEnd_2031445 < baseStart_2031445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031563 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 3, 5]
def baseStart_2031563 : Nat := 118140960795 + 2031563 * 2 ^ 59
def prefixEnd_2031563 : Nat := 4983230072969 + 3 ^ 40 * 2031563 * 2
def baseEnd_2031563 : Nat := 695445532593426822746345

theorem tailTrace_2031563 : CollatzResearch.WordTrace tailWord_2031563 prefixEnd_2031563 695445532593426822746345 := by
  unfold tailWord_2031563
  simp only [CollatzResearch.WordTrace]
  refine ⟨74097189939001689182347343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49398126626001126121564895 74097189939001689182347343)
  ·
    refine ⟨111145784908502533773521015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74097189939001689182347343 111145784908502533773521015)
    ·
      refine ⟨166718677362753800660281523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111145784908502533773521015 166718677362753800660281523)
      ·
        refine ⟨250078016044130700990422285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166718677362753800660281523 250078016044130700990422285)
        ·
          refine ⟨93779256016549012871408357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250078016044130700990422285 93779256016549012871408357)
          ·
            refine ⟨17583610503102939913389067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93779256016549012871408357 17583610503102939913389067)
            ·
              refine ⟨26375415754654409870083601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17583610503102939913389067 26375415754654409870083601)
              ·
                refine ⟨19781561815990807402562701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26375415754654409870083601 19781561815990807402562701)
                ·
                  refine ⟨7418085680996552775961013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19781561815990807402562701 7418085680996552775961013)
                  ·
                    refine ⟨695445532593426822746345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7418085680996552775961013 695445532593426822746345)
                    ·
                      rfl

theorem cell22_2031563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 5].length) (baseStart_2031563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031563 prefixEnd_2031563 := by exact prefixLift 2031563
  have htrace : WordTrace (prefixWord ++ tailWord_2031563) baseStart_2031563 baseEnd_2031563 := by
    simpa [prefixWord, tailWord_2031563, baseEnd_2031563] using wordTrace_append hprefix tailTrace_2031563
  have hstable : (prefixWord ++ tailWord_2031563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031563).length < 2 ^ (prefixWord ++ tailWord_2031563).sum := by decide
  have hdescent : baseEnd_2031563 < baseStart_2031563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031601 : List Nat := [1, 2, 2, 2, 6, 1, 2, 1, 1, 4]
def baseStart_2031601 : Nat := 118140960795 + 2031601 * 2 ^ 59
def prefixEnd_2031601 : Nat := 4983230072969 + 3 ^ 40 * 2031601 * 2
def baseEnd_2031601 : Nat := 695458540770007390296229

theorem tailTrace_2031601 : CollatzResearch.WordTrace tailWord_2031601 prefixEnd_2031601 695458540770007390296229 := by
  unfold tailWord_2031601
  simp only [CollatzResearch.WordTrace]
  refine ⟨74098575912864021672230657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49399050608576014448153771 74098575912864021672230657)
  ·
    refine ⟨55573931934648016254172993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74098575912864021672230657 55573931934648016254172993)
    ·
      refine ⟨41680448950986012190629745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55573931934648016254172993 41680448950986012190629745)
      ·
        refine ⟨31260336713239509142972309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41680448950986012190629745 31260336713239509142972309)
        ·
          refine ⟨1465328283433101991076827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31260336713239509142972309 1465328283433101991076827)
          ·
            refine ⟨2197992425149652986615241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465328283433101991076827 2197992425149652986615241)
            ·
              refine ⟨1648494318862239739961431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2197992425149652986615241 1648494318862239739961431)
              ·
                refine ⟨2472741478293359609942147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1648494318862239739961431 2472741478293359609942147)
                ·
                  refine ⟨3709112217440039414913221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2472741478293359609942147 3709112217440039414913221)
                  ·
                    refine ⟨695458540770007390296229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3709112217440039414913221 695458540770007390296229)
                    ·
                      rfl

theorem cell22_2031601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_2031601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031601 prefixEnd_2031601 := by exact prefixLift 2031601
  have htrace : WordTrace (prefixWord ++ tailWord_2031601) baseStart_2031601 baseEnd_2031601 := by
    simpa [prefixWord, tailWord_2031601, baseEnd_2031601] using wordTrace_append hprefix tailTrace_2031601
  have hstable : (prefixWord ++ tailWord_2031601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031601).length < 2 ^ (prefixWord ++ tailWord_2031601).sum := by decide
  have hdescent : baseEnd_2031601 < baseStart_2031601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031614 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_2031614 : Nat := 118140960795 + 2031614 * 2 ^ 59
def prefixEnd_2031614 : Nat := 4983230072969 + 3 ^ 40 * 2031614 * 2
def baseEnd_2031614 : Nat := 695462990935679689721189

theorem tailTrace_2031614 : CollatzResearch.WordTrace tailWord_2031614 prefixEnd_2031614 695462990935679689721189 := by
  unfold tailWord_2031614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9262381257727115611556737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49399366707877949928302597 9262381257727115611556737)
  ·
    refine ⟨6946785943295336708667553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9262381257727115611556737 6946785943295336708667553)
    ·
      refine ⟨5210089457471502531500665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6946785943295336708667553 5210089457471502531500665)
      ·
        refine ⟨3907567093103626898625499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5210089457471502531500665 3907567093103626898625499)
        ·
          refine ⟨5861350639655440347938249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3907567093103626898625499 5861350639655440347938249)
          ·
            refine ⟨4396012979741580260953687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5861350639655440347938249 4396012979741580260953687)
            ·
              refine ⟨6594019469612370391430531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4396012979741580260953687 6594019469612370391430531)
              ·
                refine ⟨9891029204418555587145797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6594019469612370391430531 9891029204418555587145797)
                ·
                  refine ⟨1854567975828479172589837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9891029204418555587145797 1854567975828479172589837)
                  ·
                    refine ⟨695462990935679689721189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1854567975828479172589837 695462990935679689721189)
                    ·
                      rfl

theorem cell22_2031614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_2031614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031614 prefixEnd_2031614 := by exact prefixLift 2031614
  have htrace : WordTrace (prefixWord ++ tailWord_2031614) baseStart_2031614 baseEnd_2031614 := by
    simpa [prefixWord, tailWord_2031614, baseEnd_2031614] using wordTrace_append hprefix tailTrace_2031614
  have hstable : (prefixWord ++ tailWord_2031614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031614).length < 2 ^ (prefixWord ++ tailWord_2031614).sum := by decide
  have hdescent : baseEnd_2031614 < baseStart_2031614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031642 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 3, 3]
def baseStart_2031642 : Nat := 118140960795 + 2031642 * 2 ^ 59
def prefixEnd_2031642 : Nat := 4983230072969 + 3 ^ 40 * 2031642 * 2
def baseEnd_2031642 : Nat := 695472575907896950021103

theorem tailTrace_2031642 : CollatzResearch.WordTrace tailWord_2031642 prefixEnd_2031642 695472575907896950021103 := by
  unfold tailWord_2031642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18525017826428871418618295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49400047537143657116315453 18525017826428871418618295)
  ·
    refine ⟨27787526739643307127927443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18525017826428871418618295 27787526739643307127927443)
    ·
      refine ⟨41681290109464960691891165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27787526739643307127927443 41681290109464960691891165)
      ·
        refine ⟨15630483791049360259459187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41681290109464960691891165 15630483791049360259459187)
        ·
          refine ⟨23445725686574040389188781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15630483791049360259459187 23445725686574040389188781)
          ·
            refine ⟨8792147132465265145945793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23445725686574040389188781 8792147132465265145945793)
            ·
              refine ⟨6594110349348948859459345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8792147132465265145945793 6594110349348948859459345)
              ·
                refine ⟨4945582762011711644594509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6594110349348948859459345 4945582762011711644594509)
                ·
                  refine ⟨1854593535754391866722941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4945582762011711644594509 1854593535754391866722941)
                  ·
                    refine ⟨695472575907896950021103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1854593535754391866722941 695472575907896950021103)
                    ·
                      rfl

theorem cell22_2031642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_2031642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031642 prefixEnd_2031642 := by exact prefixLift 2031642
  have htrace : WordTrace (prefixWord ++ tailWord_2031642) baseStart_2031642 baseEnd_2031642 := by
    simpa [prefixWord, tailWord_2031642, baseEnd_2031642] using wordTrace_append hprefix tailTrace_2031642
  have hstable : (prefixWord ++ tailWord_2031642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031642).length < 2 ^ (prefixWord ++ tailWord_2031642).sum := by decide
  have hdescent : baseEnd_2031642 < baseStart_2031642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031676 : List Nat := [2, 2, 2, 2, 2, 1, 5, 2, 1, 3]
def baseStart_2031676 : Nat := 118140960795 + 2031676 * 2 ^ 59
def prefixEnd_2031676 : Nat := 4983230072969 + 3 ^ 40 * 2031676 * 2
def baseEnd_2031676 : Nat := 695484214802732194670999

theorem tailTrace_2031676 : CollatzResearch.WordTrace tailWord_2031676 prefixEnd_2031676 695484214802732194670999 := by
  unfold tailWord_2031676
  simp only [CollatzResearch.WordTrace]
  refine ⟨37050655693796154740605441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49400874258394872987473921 37050655693796154740605441)
  ·
    refine ⟨27787991770347116055454081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37050655693796154740605441 27787991770347116055454081)
    ·
      refine ⟨20840993827760337041590561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27787991770347116055454081 20840993827760337041590561)
      ·
        refine ⟨15630745370820252781192921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20840993827760337041590561 15630745370820252781192921)
        ·
          refine ⟨11723059028115189585894691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15630745370820252781192921 11723059028115189585894691)
          ·
            refine ⟨17584588542172784378842037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11723059028115189585894691 17584588542172784378842037)
            ·
              refine ⟨1648555175828698535516441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17584588542172784378842037 1648555175828698535516441)
              ·
                refine ⟨1236416381871523901637331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648555175828698535516441 1236416381871523901637331)
                ·
                  refine ⟨1854624572807285852455997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236416381871523901637331 1854624572807285852455997)
                  ·
                    refine ⟨695484214802732194670999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1854624572807285852455997 695484214802732194670999)
                    ·
                      rfl

theorem cell22_2031676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_2031676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031676 prefixEnd_2031676 := by exact prefixLift 2031676
  have htrace : WordTrace (prefixWord ++ tailWord_2031676) baseStart_2031676 baseEnd_2031676 := by
    simpa [prefixWord, tailWord_2031676, baseEnd_2031676] using wordTrace_append hprefix tailTrace_2031676
  have hstable : (prefixWord ++ tailWord_2031676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031676).length < 2 ^ (prefixWord ++ tailWord_2031676).sum := by decide
  have hdescent : baseEnd_2031676 < baseStart_2031676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031685 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_2031685 : Nat := 118140960795 + 2031685 * 2 ^ 59
def prefixEnd_2031685 : Nat := 4983230072969 + 3 ^ 40 * 2031685 * 2
def baseEnd_2031685 : Nat := 695487295686659171195971

theorem tailTrace_2031685 : CollatzResearch.WordTrace tailWord_2031685 prefixEnd_2031685 695487295686659171195971 := by
  unfold tailWord_2031685
  simp only [CollatzResearch.WordTrace]
  refine ⟨74101639644559704018288509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49401093096373136012192339 74101639644559704018288509)
  ·
    refine ⟨27788114866709889006858191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74101639644559704018288509 27788114866709889006858191)
    ·
      refine ⟨41682172300064833510287287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27788114866709889006858191 41682172300064833510287287)
      ·
        refine ⟨62523258450097250265430931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41682172300064833510287287 62523258450097250265430931)
        ·
          refine ⟨93784887675145875398146397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62523258450097250265430931 93784887675145875398146397)
          ·
            refine ⟨35169332878179703274304899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93784887675145875398146397 35169332878179703274304899)
            ·
              refine ⟨52753999317269554911457349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35169332878179703274304899 52753999317269554911457349)
              ·
                refine ⟨9891374871988041545898253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52753999317269554911457349 9891374871988041545898253)
                ·
                  refine ⟨3709265576995515579711845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9891374871988041545898253 3709265576995515579711845)
                  ·
                    refine ⟨695487295686659171195971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3709265576995515579711845 695487295686659171195971)
                    ·
                      rfl

theorem cell22_2031685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_2031685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031685 prefixEnd_2031685 := by exact prefixLift 2031685
  have htrace : WordTrace (prefixWord ++ tailWord_2031685) baseStart_2031685 baseEnd_2031685 := by
    simpa [prefixWord, tailWord_2031685, baseEnd_2031685] using wordTrace_append hprefix tailTrace_2031685
  have hstable : (prefixWord ++ tailWord_2031685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031685).length < 2 ^ (prefixWord ++ tailWord_2031685).sum := by decide
  have hdescent : baseEnd_2031685 < baseStart_2031685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031700 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 8]
def baseStart_2031700 : Nat := 118140960795 + 2031700 * 2 ^ 59
def prefixEnd_2031700 : Nat := 4983230072969 + 3 ^ 40 * 2031700 * 2
def baseEnd_2031700 : Nat := 231830810164401377356975

theorem tailTrace_2031700 : CollatzResearch.WordTrace tailWord_2031700 prefixEnd_2031700 231830810164401377356975 := by
  unfold tailWord_2031700
  simp only [CollatzResearch.WordTrace]
  refine ⟨37051093369752680790042277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49401457826336907720056369 37051093369752680790042277)
  ·
    refine ⟨6947080006828627648132927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37051093369752680790042277 6947080006828627648132927)
    ·
      refine ⟨10420620010242941472199391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6947080006828627648132927 10420620010242941472199391)
      ·
        refine ⟨15630930015364412208299087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10420620010242941472199391 15630930015364412208299087)
        ·
          refine ⟨23446395023046618312448631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15630930015364412208299087 23446395023046618312448631)
          ·
            refine ⟨35169592534569927468672947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23446395023046618312448631 35169592534569927468672947)
            ·
              refine ⟨52754388801854891203009421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35169592534569927468672947 52754388801854891203009421)
              ·
                refine ⟨19782895800695584201128533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52754388801854891203009421 19782895800695584201128533)
                ·
                  refine ⟨231830810164401377356975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19782895800695584201128533 231830810164401377356975)
                  ·
                    rfl

theorem cell22_2031700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_2031700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031700 prefixEnd_2031700 := by exact prefixLift 2031700
  have htrace : WordTrace (prefixWord ++ tailWord_2031700) baseStart_2031700 baseEnd_2031700 := by
    simpa [prefixWord, tailWord_2031700, baseEnd_2031700] using wordTrace_append hprefix tailTrace_2031700
  have hstable : (prefixWord ++ tailWord_2031700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031700).length < 2 ^ (prefixWord ++ tailWord_2031700).sum := by decide
  have hdescent : baseEnd_2031700 < baseStart_2031700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031715 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 3, 5]
def baseStart_2031715 : Nat := 118140960795 + 2031715 * 2 ^ 59
def prefixEnd_2031715 : Nat := 4983230072969 + 3 ^ 40 * 2031715 * 2
def baseEnd_2031715 : Nat := 695497565299749092945879

theorem tailTrace_2031715 : CollatzResearch.WordTrace tailWord_2031715 prefixEnd_2031715 695497565299749092945879 := by
  unfold tailWord_2031715
  simp only [CollatzResearch.WordTrace]
  refine ⟨74102733834451019141880599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49401822556300679427920399 74102733834451019141880599)
  ·
    refine ⟨111154100751676528712820899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74102733834451019141880599 111154100751676528712820899)
    ·
      refine ⟨166731151127514793069231349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111154100751676528712820899 166731151127514793069231349)
      ·
        refine ⟨15631045418204511850240439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166731151127514793069231349 15631045418204511850240439)
        ·
          refine ⟨23446568127306767775360659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15631045418204511850240439 23446568127306767775360659)
          ·
            refine ⟨35169852190960151663040989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23446568127306767775360659 35169852190960151663040989)
            ·
              refine ⟨13188694571610056873640371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35169852190960151663040989 13188694571610056873640371)
              ·
                refine ⟨19783041857415085310460557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13188694571610056873640371 19783041857415085310460557)
                ·
                  refine ⟨7418640696530656991422709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19783041857415085310460557 7418640696530656991422709)
                  ·
                    refine ⟨695497565299749092945879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7418640696530656991422709 695497565299749092945879)
                    ·
                      rfl

theorem cell22_2031715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 5].length) (baseStart_2031715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031715 prefixEnd_2031715 := by exact prefixLift 2031715
  have htrace : WordTrace (prefixWord ++ tailWord_2031715) baseStart_2031715 baseEnd_2031715 := by
    simpa [prefixWord, tailWord_2031715, baseEnd_2031715] using wordTrace_append hprefix tailTrace_2031715
  have hstable : (prefixWord ++ tailWord_2031715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031715).length < 2 ^ (prefixWord ++ tailWord_2031715).sum := by decide
  have hdescent : baseEnd_2031715 < baseStart_2031715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031719 : List Nat := [1, 1, 5, 1, 1, 2, 5, 1, 1, 4]
def baseStart_2031719 : Nat := 118140960795 + 2031719 * 2 ^ 59
def prefixEnd_2031719 : Nat := 4983230072969 + 3 ^ 40 * 2031719 * 2
def baseEnd_2031719 : Nat := 695498934581494415845867

theorem tailTrace_2031719 : CollatzResearch.WordTrace tailWord_2031719 prefixEnd_2031719 695498934581494415845867 := by
  unfold tailWord_2031719
  simp only [CollatzResearch.WordTrace]
  refine ⟨74102879726436527825026211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49401919817624351883350807 74102879726436527825026211)
  ·
    refine ⟨111154319589654791737539317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74102879726436527825026211 111154319589654791737539317)
    ·
      refine ⟨10420717461530136725394311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111154319589654791737539317 10420717461530136725394311)
      ·
        refine ⟨15631076192295205088091467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10420717461530136725394311 15631076192295205088091467)
        ·
          refine ⟨23446614288442807632137201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15631076192295205088091467 23446614288442807632137201)
          ·
            refine ⟨17584960716332105724102901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23446614288442807632137201 17584960716332105724102901)
            ·
              refine ⟨1648590067156134911634647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17584960716332105724102901 1648590067156134911634647)
              ·
                refine ⟨2472885100734202367451971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1648590067156134911634647 2472885100734202367451971)
                ·
                  refine ⟨3709327651101303551177957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2472885100734202367451971 3709327651101303551177957)
                  ·
                    refine ⟨695498934581494415845867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3709327651101303551177957 695498934581494415845867)
                    ·
                      rfl

theorem cell22_2031719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_2031719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031719 prefixEnd_2031719 := by exact prefixLift 2031719
  have htrace : WordTrace (prefixWord ++ tailWord_2031719) baseStart_2031719 baseEnd_2031719 := by
    simpa [prefixWord, tailWord_2031719, baseEnd_2031719] using wordTrace_append hprefix tailTrace_2031719
  have hstable : (prefixWord ++ tailWord_2031719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031719).length < 2 ^ (prefixWord ++ tailWord_2031719).sum := by decide
  have hdescent : baseEnd_2031719 < baseStart_2031719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031749 : List Nat := [1, 3, 1, 1, 5, 1, 2, 3, 2, 3]
def baseStart_2031749 : Nat := 118140960795 + 2031749 * 2 ^ 59
def prefixEnd_2031749 : Nat := 4983230072969 + 3 ^ 40 * 2031749 * 2
def baseEnd_2031749 : Nat := 695509204194584337595775

theorem tailTrace_2031749 : CollatzResearch.WordTrace tailWord_2031749 prefixEnd_2031749 695509204194584337595775 := by
  unfold tailWord_2031749
  simp only [CollatzResearch.WordTrace]
  refine ⟨74103973916327842948618301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49402649277551895299078867 74103973916327842948618301)
  ·
    refine ⟨27788990218622941105731863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74103973916327842948618301 27788990218622941105731863)
    ·
      refine ⟨41683485327934411658597795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27788990218622941105731863 41683485327934411658597795)
      ·
        refine ⟨62525227991901617487896693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41683485327934411658597795 62525227991901617487896693)
        ·
          refine ⟨5861740124240776639490315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62525227991901617487896693 5861740124240776639490315)
          ·
            refine ⟨8792610186361164959235473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5861740124240776639490315 8792610186361164959235473)
            ·
              refine ⟨6594457639770873719426605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8792610186361164959235473 6594457639770873719426605)
              ·
                refine ⟨2472921614914077644784977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6594457639770873719426605 2472921614914077644784977)
                ·
                  refine ⟨1854691211185558233588733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2472921614914077644784977 1854691211185558233588733)
                  ·
                    refine ⟨695509204194584337595775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1854691211185558233588733 695509204194584337595775)
                    ·
                      rfl

theorem cell22_2031749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_2031749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031749 prefixEnd_2031749 := by exact prefixLift 2031749
  have htrace : WordTrace (prefixWord ++ tailWord_2031749) baseStart_2031749 baseEnd_2031749 := by
    simpa [prefixWord, tailWord_2031749, baseEnd_2031749] using wordTrace_append hprefix tailTrace_2031749
  have hstable : (prefixWord ++ tailWord_2031749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031749).length < 2 ^ (prefixWord ++ tailWord_2031749).sum := by decide
  have hdescent : baseEnd_2031749 < baseStart_2031749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031783 : List Nat := [1, 1, 6, 2, 2, 2, 1, 2, 2, 3]
def baseStart_2031783 : Nat := 118140960795 + 2031783 * 2 ^ 59
def prefixEnd_2031783 : Nat := 4983230072969 + 3 ^ 40 * 2031783 * 2
def baseEnd_2031783 : Nat := 695520843089419582245671

theorem tailTrace_2031783 : CollatzResearch.WordTrace tailWord_2031783 prefixEnd_2031783 695520843089419582245671 := by
  unfold tailWord_2031783
  simp only [CollatzResearch.WordTrace]
  refine ⟨74105213998204666755356003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49403475998803111170237335 74105213998204666755356003)
  ·
    refine ⟨111157820997307000133034005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74105213998204666755356003 111157820997307000133034005)
    ·
      refine ⟨5210522859248765631235969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111157820997307000133034005 5210522859248765631235969)
      ·
        refine ⟨3907892144436574223426977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5210522859248765631235969 3907892144436574223426977)
        ·
          refine ⟨2930919108327430667570233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3907892144436574223426977 2930919108327430667570233)
          ·
            refine ⟨2198189331245573000677675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2930919108327430667570233 2198189331245573000677675)
            ·
              refine ⟨3297283996868359501016513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198189331245573000677675 3297283996868359501016513)
              ·
                refine ⟨2472962997651269625762385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3297283996868359501016513 2472962997651269625762385)
                ·
                  refine ⟨1854722248238452219321789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2472962997651269625762385 1854722248238452219321789)
                  ·
                    refine ⟨695520843089419582245671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1854722248238452219321789 695520843089419582245671)
                    ·
                      rfl

theorem cell22_2031783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_2031783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031783 prefixEnd_2031783 := by exact prefixLift 2031783
  have htrace : WordTrace (prefixWord ++ tailWord_2031783) baseStart_2031783 baseEnd_2031783 := by
    simpa [prefixWord, tailWord_2031783, baseEnd_2031783] using wordTrace_append hprefix tailTrace_2031783
  have hstable : (prefixWord ++ tailWord_2031783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031783).length < 2 ^ (prefixWord ++ tailWord_2031783).sum := by decide
  have hdescent : baseEnd_2031783 < baseStart_2031783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031794 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_2031794 : Nat := 118140960795 + 2031794 * 2 ^ 59
def prefixEnd_2031794 : Nat := 4983230072969 + 3 ^ 40 * 2031794 * 2
def baseEnd_2031794 : Nat := 695524608614219220220637

theorem tailTrace_2031794 : CollatzResearch.WordTrace tailWord_2031794 prefixEnd_2031794 695524608614219220220637 := by
  unfold tailWord_2031794
  simp only [CollatzResearch.WordTrace]
  refine ⟨18526403800291203908501609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49403743467443210422670957 18526403800291203908501609)
  ·
    refine ⟨13894802850218402931376207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18526403800291203908501609 13894802850218402931376207)
    ·
      refine ⟨20842204275327604397064311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13894802850218402931376207 20842204275327604397064311)
      ·
        refine ⟨31263306412991406595596467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20842204275327604397064311 31263306412991406595596467)
        ·
          refine ⟨46894959619487109893394701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31263306412991406595596467 46894959619487109893394701)
          ·
            refine ⟨17585609857307666210023013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46894959619487109893394701 17585609857307666210023013)
            ·
              refine ⟨3297301848245187414379315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17585609857307666210023013 3297301848245187414379315)
              ·
                refine ⟨4945952772367781121568973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3297301848245187414379315 4945952772367781121568973)
                ·
                  refine ⟨1854732289637917920588365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4945952772367781121568973 1854732289637917920588365)
                  ·
                    refine ⟨695524608614219220220637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1854732289637917920588365 695524608614219220220637)
                    ·
                      rfl

theorem cell22_2031794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_2031794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031794 prefixEnd_2031794 := by exact prefixLift 2031794
  have htrace : WordTrace (prefixWord ++ tailWord_2031794) baseStart_2031794 baseEnd_2031794 := by
    simpa [prefixWord, tailWord_2031794, baseEnd_2031794] using wordTrace_append hprefix tailTrace_2031794
  have hstable : (prefixWord ++ tailWord_2031794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031794).length < 2 ^ (prefixWord ++ tailWord_2031794).sum := by decide
  have hdescent : baseEnd_2031794 < baseStart_2031794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031835 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 10]
def baseStart_2031835 : Nat := 118140960795 + 2031835 * 2 ^ 59
def prefixEnd_2031835 : Nat := 4983230072969 + 3 ^ 40 * 2031835 * 2
def baseEnd_2031835 : Nat := 231846214584036259981837

theorem tailTrace_2031835 : CollatzResearch.WordTrace tailWord_2031835 prefixEnd_2031835 231846214584036259981837 := by
  unfold tailWord_2031835
  simp only [CollatzResearch.WordTrace]
  refine ⟨74107110594016279636248959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49404740396010853090832639 74107110594016279636248959)
  ·
    refine ⟨111160665891024419454373439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74107110594016279636248959 111160665891024419454373439)
    ·
      refine ⟨166740998836536629181560159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111160665891024419454373439 166740998836536629181560159)
      ·
        refine ⟨250111498254804943772340239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166740998836536629181560159 250111498254804943772340239)
        ·
          refine ⟨375167247382207415658510359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250111498254804943772340239 375167247382207415658510359)
          ·
            refine ⟨562750871073311123487765539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375167247382207415658510359 562750871073311123487765539)
            ·
              refine ⟨844126306609966685231648309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562750871073311123487765539 844126306609966685231648309)
              ·
                refine ⟨79136841244684376740467029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 844126306609966685231648309 79136841244684376740467029)
                ·
                  refine ⟨231846214584036259981837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 79136841244684376740467029 231846214584036259981837)
                  ·
                    rfl

theorem cell22_2031835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 10].length) (baseStart_2031835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031835 prefixEnd_2031835 := by exact prefixLift 2031835
  have htrace : WordTrace (prefixWord ++ tailWord_2031835) baseStart_2031835 baseEnd_2031835 := by
    simpa [prefixWord, tailWord_2031835, baseEnd_2031835] using wordTrace_append hprefix tailTrace_2031835
  have hstable : (prefixWord ++ tailWord_2031835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031835).length < 2 ^ (prefixWord ++ tailWord_2031835).sum := by decide
  have hdescent : baseEnd_2031835 < baseStart_2031835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031882 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_2031882 : Nat := 118140960795 + 2031882 * 2 ^ 59
def prefixEnd_2031882 : Nat := 4983230072969 + 3 ^ 40 * 2031882 * 2
def baseEnd_2031882 : Nat := 695554732812616324020367

theorem tailTrace_2031882 : CollatzResearch.WordTrace tailWord_2031882 prefixEnd_2031882 695554732812616324020367 := by
  unfold tailWord_2031882
  simp only [CollatzResearch.WordTrace]
  refine ⟨18527206206211501665802475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49405883216564004442139933 18527206206211501665802475)
  ·
    refine ⟨27790809309317252498703713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18527206206211501665802475 27790809309317252498703713)
    ·
      refine ⟨20843106981987939374027785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27790809309317252498703713 20843106981987939374027785)
      ·
        refine ⟨15632330236490954530520839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20843106981987939374027785 15632330236490954530520839)
        ·
          refine ⟨23448495354736431795781259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15632330236490954530520839 23448495354736431795781259)
          ·
            refine ⟨35172743032104647693671889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23448495354736431795781259 35172743032104647693671889)
            ·
              refine ⟨26379557274078485770253917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35172743032104647693671889 26379557274078485770253917)
              ·
                refine ⟨9892333977779432163845219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26379557274078485770253917 9892333977779432163845219)
                ·
                  refine ⟨14838500966669148245767829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9892333977779432163845219 14838500966669148245767829)
                  ·
                    refine ⟨695554732812616324020367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14838500966669148245767829 695554732812616324020367)
                    ·
                      rfl

theorem cell22_2031882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_2031882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031882 prefixEnd_2031882 := by exact prefixLift 2031882
  have htrace : WordTrace (prefixWord ++ tailWord_2031882) baseStart_2031882 baseEnd_2031882 := by
    simpa [prefixWord, tailWord_2031882, baseEnd_2031882] using wordTrace_append hprefix tailTrace_2031882
  have hstable : (prefixWord ++ tailWord_2031882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031882).length < 2 ^ (prefixWord ++ tailWord_2031882).sum := by decide
  have hdescent : baseEnd_2031882 < baseStart_2031882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031903 : List Nat := [1, 1, 2, 4, 3, 3, 2, 2, 4]
def baseStart_2031903 : Nat := 118140960795 + 2031903 * 2 ^ 59
def prefixEnd_2031903 : Nat := 4983230072969 + 3 ^ 40 * 2031903 * 2
def baseEnd_2031903 : Nat := 231853973847259756415101

theorem tailTrace_2031903 : CollatzResearch.WordTrace tailWord_2031903 prefixEnd_2031903 231853973847259756415101 := by
  unfold tailWord_2031903
  simp only [CollatzResearch.WordTrace]
  refine ⟨74109590757769927249724363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49406393838513284833149575 74109590757769927249724363)
  ·
    refine ⟨111164386136654890874586545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74109590757769927249724363 111164386136654890874586545)
    ·
      refine ⟨83373289602491168155939909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111164386136654890874586545 83373289602491168155939909)
      ·
        refine ⟨15632491800467094029238733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83373289602491168155939909 15632491800467094029238733)
        ·
          refine ⟨5862184425175160260964525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15632491800467094029238733 5862184425175160260964525)
          ·
            refine ⟨2198319159440685097861697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5862184425175160260964525 2198319159440685097861697)
            ·
              refine ⟨1648739369580513823396273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2198319159440685097861697 1648739369580513823396273)
              ·
                refine ⟨1236554527185385367547205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648739369580513823396273 1236554527185385367547205)
                ·
                  refine ⟨231853973847259756415101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1236554527185385367547205 231853973847259756415101)
                  ·
                    rfl

theorem cell22_2031903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 4].length) (baseStart_2031903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031903 prefixEnd_2031903 := by exact prefixLift 2031903
  have htrace : WordTrace (prefixWord ++ tailWord_2031903) baseStart_2031903 baseEnd_2031903 := by
    simpa [prefixWord, tailWord_2031903, baseEnd_2031903] using wordTrace_append hprefix tailTrace_2031903
  have hstable : (prefixWord ++ tailWord_2031903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031903).length < 2 ^ (prefixWord ++ tailWord_2031903).sum := by decide
  have hdescent : baseEnd_2031903 < baseStart_2031903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031918 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_2031918 : Nat := 118140960795 + 2031918 * 2 ^ 59
def prefixEnd_2031918 : Nat := 4983230072969 + 3 ^ 40 * 2031918 * 2
def baseEnd_2031918 : Nat := 695567056348324230120257

theorem tailTrace_2031918 : CollatzResearch.WordTrace tailWord_2031918 prefixEnd_2031918 695567056348324230120257 := by
  unfold tailWord_2031918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9263767231589448101440051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49406758568477056541013605 9263767231589448101440051)
  ·
    refine ⟨13895650847384172152160077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9263767231589448101440051 13895650847384172152160077)
    ·
      refine ⟨5210869067769064557060029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13895650847384172152160077 5210869067769064557060029)
      ·
        refine ⟨1954075900413399208897511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5210869067769064557060029 1954075900413399208897511)
        ·
          refine ⟨2931113850620098813346267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1954075900413399208897511 2931113850620098813346267)
          ·
            refine ⟨4396670775930148220019401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931113850620098813346267 4396670775930148220019401)
            ·
              refine ⟨3297503081947611165014551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4396670775930148220019401 3297503081947611165014551)
              ·
                refine ⟨4946254622921416747521827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3297503081947611165014551 4946254622921416747521827)
                ·
                  refine ⟨7419381934382125121282741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946254622921416747521827 7419381934382125121282741)
                  ·
                    refine ⟨695567056348324230120257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7419381934382125121282741 695567056348324230120257)
                    ·
                      rfl

theorem cell22_2031918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_2031918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2031918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2031918 prefixEnd_2031918 := by exact prefixLift 2031918
  have htrace : WordTrace (prefixWord ++ tailWord_2031918) baseStart_2031918 baseEnd_2031918 := by
    simpa [prefixWord, tailWord_2031918, baseEnd_2031918] using wordTrace_append hprefix tailTrace_2031918
  have hstable : (prefixWord ++ tailWord_2031918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031918).length < 2 ^ (prefixWord ++ tailWord_2031918).sum := by decide
  have hdescent : baseEnd_2031918 < baseStart_2031918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032040 : List Nat := [2, 1, 6, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2032040 : Nat := 118140960795 + 2032040 * 2 ^ 59
def prefixEnd_2032040 : Nat := 4983230072969 + 3 ^ 40 * 2032040 * 2
def baseEnd_2032040 : Nat := 695608819441556578569883

theorem tailTrace_2032040 : CollatzResearch.WordTrace tailWord_2032040 prefixEnd_2032040 695608819441556578569883 := by
  unfold tailWord_2032040
  simp only [CollatzResearch.WordTrace]
  refine ⟨37057293779136799823730787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49409725038849066431641049 37057293779136799823730787)
  ·
    refine ⟨55585940668705199735596181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37057293779136799823730787 55585940668705199735596181)
    ·
      refine ⟨2605590968845556237606071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55585940668705199735596181 2605590968845556237606071)
      ·
        refine ⟨3908386453268334356409107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2605590968845556237606071 3908386453268334356409107)
        ·
          refine ⟨5862579679902501534613661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3908386453268334356409107 5862579679902501534613661)
          ·
            refine ⟨2198467379963438075480123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5862579679902501534613661 2198467379963438075480123)
            ·
              refine ⟨3297701069945157113220185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198467379963438075480123 3297701069945157113220185)
              ·
                refine ⟨2473275802458867834915139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3297701069945157113220185 2473275802458867834915139)
                ·
                  refine ⟨3709913703688301752372709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473275802458867834915139 3709913703688301752372709)
                  ·
                    refine ⟨695608819441556578569883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3709913703688301752372709 695608819441556578569883)
                    ·
                      rfl

theorem cell22_2032040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2032040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032040 prefixEnd_2032040 := by exact prefixLift 2032040
  have htrace : WordTrace (prefixWord ++ tailWord_2032040) baseStart_2032040 baseEnd_2032040 := by
    simpa [prefixWord, tailWord_2032040, baseEnd_2032040] using wordTrace_append hprefix tailTrace_2032040
  have hstable : (prefixWord ++ tailWord_2032040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032040).length < 2 ^ (prefixWord ++ tailWord_2032040).sum := by decide
  have hdescent : baseEnd_2032040 < baseStart_2032040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032049 : List Nat := [1, 2, 2, 4, 1, 2, 2, 8]
def baseStart_2032049 : Nat := 118140960795 + 2032049 * 2 ^ 59
def prefixEnd_2032049 : Nat := 4983230072969 + 3 ^ 40 * 2032049 * 2
def baseEnd_2032049 : Nat := 77290211147275950566095

theorem tailTrace_2032049 : CollatzResearch.WordTrace tailWord_2032049 prefixEnd_2032049 77290211147275950566095 := by
  unfold tailWord_2032049
  simp only [CollatzResearch.WordTrace]
  refine ⟨74114915815240994184539201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49409943876827329456359467 74114915815240994184539201)
  ·
    refine ⟨55586186861430745638404401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74114915815240994184539201 55586186861430745638404401)
    ·
      refine ⟨41689640146073059228803301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55586186861430745638404401 41689640146073059228803301)
      ·
        refine ⟨7816807527388698605400619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41689640146073059228803301 7816807527388698605400619)
        ·
          refine ⟨11725211291083047908100929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7816807527388698605400619 11725211291083047908100929)
          ·
            refine ⟨8793908468312285931075697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11725211291083047908100929 8793908468312285931075697)
            ·
              refine ⟨6595431351234214448306773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8793908468312285931075697 6595431351234214448306773)
              ·
                refine ⟨77290211147275950566095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6595431351234214448306773 77290211147275950566095)
                ·
                  rfl

theorem cell22_2032049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 8].length) (baseStart_2032049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032049 prefixEnd_2032049 := by exact prefixLift 2032049
  have htrace : WordTrace (prefixWord ++ tailWord_2032049) baseStart_2032049 baseEnd_2032049 := by
    simpa [prefixWord, tailWord_2032049, baseEnd_2032049] using wordTrace_append hprefix tailTrace_2032049
  have hstable : (prefixWord ++ tailWord_2032049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032049).length < 2 ^ (prefixWord ++ tailWord_2032049).sum := by decide
  have hdescent : baseEnd_2032049 < baseStart_2032049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032156 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 6]
def baseStart_2032156 : Nat := 118140960795 + 2032156 * 2 ^ 59
def prefixEnd_2032156 : Nat := 4983230072969 + 3 ^ 40 * 2032156 * 2
def baseEnd_2032156 : Nat := 231882842870723647556509

theorem tailTrace_2032156 : CollatzResearch.WordTrace tailWord_2032156 prefixEnd_2032156 231882842870723647556509 := by
  unfold tailWord_2032156
  simp only [CollatzResearch.WordTrace]
  refine ⟨37059409212926675729342161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49412545617235567639122881 37059409212926675729342161)
  ·
    refine ⟨27794556909695006797006621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37059409212926675729342161 27794556909695006797006621)
    ·
      refine ⟨10422958841135627548877483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27794556909695006797006621 10422958841135627548877483)
      ·
        refine ⟨15634438261703441323316225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10422958841135627548877483 15634438261703441323316225)
        ·
          refine ⟨11725828696277580992487169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15634438261703441323316225 11725828696277580992487169)
          ·
            refine ⟨8794371522208185744365377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11725828696277580992487169 8794371522208185744365377)
            ·
              refine ⟨6595778641656139308274033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8794371522208185744365377 6595778641656139308274033)
              ·
                refine ⟨4946833981242104481205525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6595778641656139308274033 4946833981242104481205525)
                ·
                  refine ⟨231882842870723647556509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4946833981242104481205525 231882842870723647556509)
                  ·
                    rfl

theorem cell22_2032156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_2032156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032156 prefixEnd_2032156 := by exact prefixLift 2032156
  have htrace : WordTrace (prefixWord ++ tailWord_2032156) baseStart_2032156 baseEnd_2032156 := by
    simpa [prefixWord, tailWord_2032156, baseEnd_2032156] using wordTrace_append hprefix tailTrace_2032156
  have hstable : (prefixWord ++ tailWord_2032156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032156).length < 2 ^ (prefixWord ++ tailWord_2032156).sum := by decide
  have hdescent : baseEnd_2032156 < baseStart_2032156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032186 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_2032186 : Nat := 118140960795 + 2032186 * 2 ^ 59
def prefixEnd_2032186 : Nat := 4983230072969 + 3 ^ 40 * 2032186 * 2
def baseEnd_2032186 : Nat := 695658798225260864419435

theorem tailTrace_2032186 : CollatzResearch.WordTrace tailWord_2032186 prefixEnd_2032186 695658798225260864419435 := by
  unfold tailWord_2032186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18529978153936166645569103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49413275077163111054850941 18529978153936166645569103)
  ·
    refine ⟨27794967230904249968353655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18529978153936166645569103 27794967230904249968353655)
    ·
      refine ⟨41692450846356374952530483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27794967230904249968353655 41692450846356374952530483)
      ·
        refine ⟨62538676269534562428795725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41692450846356374952530483 62538676269534562428795725)
        ·
          refine ⟨23452003601075460910798397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62538676269534562428795725 23452003601075460910798397)
          ·
            refine ⟨8794501350403297841549399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23452003601075460910798397 8794501350403297841549399)
            ·
              refine ⟨13191752025604946762324099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8794501350403297841549399 13191752025604946762324099)
              ·
                refine ⟨19787628038407420143486149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13191752025604946762324099 19787628038407420143486149)
                ·
                  refine ⟨3710180257201391276903653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19787628038407420143486149 3710180257201391276903653)
                  ·
                    refine ⟨695658798225260864419435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3710180257201391276903653 695658798225260864419435)
                    ·
                      rfl

theorem cell22_2032186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_2032186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032186 prefixEnd_2032186 := by exact prefixLift 2032186
  have htrace : WordTrace (prefixWord ++ tailWord_2032186) baseStart_2032186 baseEnd_2032186 := by
    simpa [prefixWord, tailWord_2032186, baseEnd_2032186] using wordTrace_append hprefix tailTrace_2032186
  have hstable : (prefixWord ++ tailWord_2032186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032186).length < 2 ^ (prefixWord ++ tailWord_2032186).sum := by decide
  have hdescent : baseEnd_2032186 < baseStart_2032186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032188 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 4, 3]
def baseStart_2032188 : Nat := 118140960795 + 2032188 * 2 ^ 59
def prefixEnd_2032188 : Nat := 4983230072969 + 3 ^ 40 * 2032188 * 2
def baseEnd_2032188 : Nat := 695659482866133525869429

theorem tailTrace_2032188 : CollatzResearch.WordTrace tailWord_2032188 prefixEnd_2032188 695659482866133525869429 := by
  unfold tailWord_2032188
  simp only [CollatzResearch.WordTrace]
  refine ⟨37059992780868710461924609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49413323707824947282566145 37059992780868710461924609)
  ·
    refine ⟨27794994585651532846443457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37059992780868710461924609 27794994585651532846443457)
    ·
      refine ⟨20846245939238649634832593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27794994585651532846443457 20846245939238649634832593)
      ·
        refine ⟨15634684454428987226124445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20846245939238649634832593 15634684454428987226124445)
        ·
          refine ⟨5863006670410870209796667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15634684454428987226124445 5863006670410870209796667)
          ·
            refine ⟨8794510005616305314695001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5863006670410870209796667 8794510005616305314695001)
            ·
              refine ⟨6595882504212228986021251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8794510005616305314695001 6595882504212228986021251)
              ·
                refine ⟨9893823756318343479031877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6595882504212228986021251 9893823756318343479031877)
                ·
                  refine ⟨1855091954309689402318477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9893823756318343479031877 1855091954309689402318477)
                  ·
                    refine ⟨695659482866133525869429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1855091954309689402318477 695659482866133525869429)
                    ·
                      rfl

theorem cell22_2032188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_2032188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032188 prefixEnd_2032188 := by exact prefixLift 2032188
  have htrace : WordTrace (prefixWord ++ tailWord_2032188) baseStart_2032188 baseEnd_2032188 := by
    simpa [prefixWord, tailWord_2032188, baseEnd_2032188] using wordTrace_append hprefix tailTrace_2032188
  have hstable : (prefixWord ++ tailWord_2032188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032188).length < 2 ^ (prefixWord ++ tailWord_2032188).sum := by decide
  have hdescent : baseEnd_2032188 < baseStart_2032188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032196 : List Nat := [2, 3, 5, 1, 2, 1, 2, 1, 5]
def baseStart_2032196 : Nat := 118140960795 + 2032196 * 2 ^ 59
def prefixEnd_2032196 : Nat := 4983230072969 + 3 ^ 40 * 2032196 * 2
def baseEnd_2032196 : Nat := 231887407143208057223135

theorem tailTrace_2032196 : CollatzResearch.WordTrace tailWord_2032196 prefixEnd_2032196 231887407143208057223135 := by
  unfold tailWord_2032196
  simp only [CollatzResearch.WordTrace]
  refine ⟨37060138672854219145070221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49413518230472292193426961 37060138672854219145070221)
  ·
    refine ⟨13897552002320332179401333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37060138672854219145070221 13897552002320332179401333)
    ·
      refine ⟨1302895500217531141818875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13897552002320332179401333 1302895500217531141818875)
      ·
        refine ⟨1954343250326296712728313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1302895500217531141818875 1954343250326296712728313)
        ·
          refine ⟨1465757437744722534546235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1954343250326296712728313 1465757437744722534546235)
          ·
            refine ⟨2198636156617083801819353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465757437744722534546235 2198636156617083801819353)
            ·
              refine ⟨1648977117462812851364515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2198636156617083801819353 1648977117462812851364515)
              ·
                refine ⟨2473465676194219277046773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1648977117462812851364515 2473465676194219277046773)
                ·
                  refine ⟨231887407143208057223135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2473465676194219277046773 231887407143208057223135)
                  ·
                    rfl

theorem cell22_2032196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_2032196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032196 prefixEnd_2032196 := by exact prefixLift 2032196
  have htrace : WordTrace (prefixWord ++ tailWord_2032196) baseStart_2032196 baseEnd_2032196 := by
    simpa [prefixWord, tailWord_2032196, baseEnd_2032196] using wordTrace_append hprefix tailTrace_2032196
  have hstable : (prefixWord ++ tailWord_2032196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032196).length < 2 ^ (prefixWord ++ tailWord_2032196).sum := by decide
  have hdescent : baseEnd_2032196 < baseStart_2032196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032220 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 2, 4]
def baseStart_2032220 : Nat := 118140960795 + 2032220 * 2 ^ 59
def prefixEnd_2032220 : Nat := 4983230072969 + 3 ^ 40 * 2032220 * 2
def baseEnd_2032220 : Nat := 695670437120096109069331

theorem tailTrace_2032220 : CollatzResearch.WordTrace tailWord_2032220 prefixEnd_2032220 695670437120096109069331 := by
  unfold tailWord_2032220
  simp only [CollatzResearch.WordTrace]
  refine ⟨37060576348810745194507057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49414101798414326926009409 37060576348810745194507057)
  ·
    refine ⟨27795432261608058895880293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37060576348810745194507057 27795432261608058895880293)
    ·
      refine ⟨5211643549051511042977555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27795432261608058895880293 5211643549051511042977555)
      ·
        refine ⟨7817465323577266564466333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5211643549051511042977555 7817465323577266564466333)
        ·
          refine ⟨2931549496341474961674875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7817465323577266564466333 2931549496341474961674875)
          ·
            refine ⟨4397324244512212442512313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931549496341474961674875 4397324244512212442512313)
            ·
              refine ⟨3297993183384159331884235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4397324244512212442512313 3297993183384159331884235)
              ·
                refine ⟨4946989775076238997826353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3297993183384159331884235 4946989775076238997826353)
                ·
                  refine ⟨3710242331307179248369765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4946989775076238997826353 3710242331307179248369765)
                  ·
                    refine ⟨695670437120096109069331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3710242331307179248369765 695670437120096109069331)
                    ·
                      rfl

theorem cell22_2032220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_2032220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032220 prefixEnd_2032220 := by exact prefixLift 2032220
  have htrace : WordTrace (prefixWord ++ tailWord_2032220) baseStart_2032220 baseEnd_2032220 := by
    simpa [prefixWord, tailWord_2032220, baseEnd_2032220] using wordTrace_append hprefix tailTrace_2032220
  have hstable : (prefixWord ++ tailWord_2032220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032220).length < 2 ^ (prefixWord ++ tailWord_2032220).sum := by decide
  have hdescent : baseEnd_2032220 < baseStart_2032220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032261 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_2032261 : Nat := 118140960795 + 2032261 * 2 ^ 59
def prefixEnd_2032261 : Nat := 4983230072969 + 3 ^ 40 * 2032261 * 2
def baseEnd_2032261 : Nat := 695684472257985668794205

theorem tailTrace_2032261 : CollatzResearch.WordTrace tailWord_2032261 prefixEnd_2032261 695684472257985668794205 := by
  unfold tailWord_2032261
  simp only [CollatzResearch.WordTrace]
  refine ⟨74122648090472954391256637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49415098726981969594171091 74122648090472954391256637)
  ·
    refine ⟨27795993033927357896721239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74122648090472954391256637 27795993033927357896721239)
    ·
      refine ⟨41693989550891036845081859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27795993033927357896721239 41693989550891036845081859)
      ·
        refine ⟨62540984326336555267622789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41693989550891036845081859 62540984326336555267622789)
        ·
          refine ⟨11726434561188104112679273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62540984326336555267622789 11726434561188104112679273)
          ·
            refine ⟨8794825920891078084509455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11726434561188104112679273 8794825920891078084509455)
            ·
              refine ⟨13192238881336617126764183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8794825920891078084509455 13192238881336617126764183)
              ·
                refine ⟨19788358322004925690146275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13192238881336617126764183 19788358322004925690146275)
                ·
                  refine ⟨29682537483007388535219413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19788358322004925690146275 29682537483007388535219413)
                  ·
                    refine ⟨695684472257985668794205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29682537483007388535219413 695684472257985668794205)
                    ·
                      rfl

theorem cell22_2032261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_2032261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032261 prefixEnd_2032261 := by exact prefixLift 2032261
  have htrace : WordTrace (prefixWord ++ tailWord_2032261) baseStart_2032261 baseEnd_2032261 := by
    simpa [prefixWord, tailWord_2032261, baseEnd_2032261] using wordTrace_append hprefix tailTrace_2032261
  have hstable : (prefixWord ++ tailWord_2032261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032261).length < 2 ^ (prefixWord ++ tailWord_2032261).sum := by decide
  have hdescent : baseEnd_2032261 < baseStart_2032261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032353 : List Nat := [1, 2, 3, 1, 4, 3, 8]
def baseStart_2032353 : Nat := 118140960795 + 2032353 * 2 ^ 59
def prefixEnd_2032353 : Nat := 4983230072969 + 3 ^ 40 * 2032353 * 2
def baseEnd_2032353 : Nat := 25767257990301040573849

theorem tailTrace_2032353 : CollatzResearch.WordTrace tailWord_2032353 prefixEnd_2032353 25767257990301040573849 := by
  unfold tailWord_2032353
  simp only [CollatzResearch.WordTrace]
  refine ⟨74126003606139654103605713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49417335737426436069070475 74126003606139654103605713)
  ·
    refine ⟨55594502704604740577704285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74126003606139654103605713 55594502704604740577704285)
    ·
      refine ⟨20847938514226777716639107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55594502704604740577704285 20847938514226777716639107)
      ·
        refine ⟨31271907771340166574958661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20847938514226777716639107 31271907771340166574958661)
        ·
          refine ⟨5863482707126281232804749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31271907771340166574958661 5863482707126281232804749)
          ·
            refine ⟨2198806015172355462301781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5863482707126281232804749 2198806015172355462301781)
            ·
              refine ⟨25767257990301040573849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2198806015172355462301781 25767257990301040573849)
              ·
                rfl

theorem cell22_2032353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 8].length) (baseStart_2032353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032353 prefixEnd_2032353 := by exact prefixLift 2032353
  have htrace : WordTrace (prefixWord ++ tailWord_2032353) baseStart_2032353 baseEnd_2032353 := by
    simpa [prefixWord, tailWord_2032353, baseEnd_2032353] using wordTrace_append hprefix tailTrace_2032353
  have hstable : (prefixWord ++ tailWord_2032353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032353).length < 2 ^ (prefixWord ++ tailWord_2032353).sum := by decide
  have hdescent : baseEnd_2032353 < baseStart_2032353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032355 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 2, 4]
def baseStart_2032355 : Nat := 118140960795 + 2032355 * 2 ^ 59
def prefixEnd_2032355 : Nat := 4983230072969 + 3 ^ 40 * 2032355 * 2
def baseEnd_2032355 : Nat := 695716650379000756943917

theorem tailTrace_2032355 : CollatzResearch.WordTrace tailWord_2032355 prefixEnd_2032355 695716650379000756943917 := by
  unfold tailWord_2032355
  simp only [CollatzResearch.WordTrace]
  refine ⟨74126076552132408445178519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49417384368088272296785679 74126076552132408445178519)
  ·
    refine ⟨111189114828198612667767779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74126076552132408445178519 111189114828198612667767779)
    ·
      refine ⟨166783672242297919001651669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111189114828198612667767779 166783672242297919001651669)
      ·
        refine ⟨3908992318178857476601211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 166783672242297919001651669 3908992318178857476601211)
        ·
          refine ⟨5863488477268286214901817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3908992318178857476601211 5863488477268286214901817)
          ·
            refine ⟨4397616357951214661176363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5863488477268286214901817 4397616357951214661176363)
            ·
              refine ⟨6596424536926821991764545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397616357951214661176363 6596424536926821991764545)
              ·
                refine ⟨4947318402695116493823409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6596424536926821991764545 4947318402695116493823409)
                ·
                  refine ⟨3710488802021337370367557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4947318402695116493823409 3710488802021337370367557)
                  ·
                    refine ⟨695716650379000756943917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3710488802021337370367557 695716650379000756943917)
                    ·
                      rfl

theorem cell22_2032355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 4].length) (baseStart_2032355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032355 prefixEnd_2032355 := by exact prefixLift 2032355
  have htrace : WordTrace (prefixWord ++ tailWord_2032355) baseStart_2032355 baseEnd_2032355 := by
    simpa [prefixWord, tailWord_2032355, baseEnd_2032355] using wordTrace_append hprefix tailTrace_2032355
  have hstable : (prefixWord ++ tailWord_2032355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032355).length < 2 ^ (prefixWord ++ tailWord_2032355).sum := by decide
  have hdescent : baseEnd_2032355 < baseStart_2032355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032415 : List Nat := [1, 1, 2, 4, 2, 3, 2, 2, 5]
def baseStart_2032415 : Nat := 118140960795 + 2032415 * 2 ^ 59
def prefixEnd_2032415 : Nat := 4983230072969 + 3 ^ 40 * 2032415 * 2
def baseEnd_2032415 : Nat := 231912396535060200147911

theorem tailTrace_2032415 : CollatzResearch.WordTrace tailWord_2032415 prefixEnd_2032415 231912396535060200147911 := by
  unfold tailWord_2032415
  simp only [CollatzResearch.WordTrace]
  refine ⟨74128264931915038692362699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49418843287943359128241799 74128264931915038692362699)
  ·
    refine ⟨111192397397872558038544049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74128264931915038692362699 111192397397872558038544049)
    ·
      refine ⟨83394298048404418528908037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111192397397872558038544049 83394298048404418528908037)
      ·
        refine ⟨15636430884075828474170257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83394298048404418528908037 15636430884075828474170257)
        ·
          refine ⟨11727323163056871355627693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15636430884075828474170257 11727323163056871355627693)
          ·
            refine ⟨4397746186146326758360385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11727323163056871355627693 4397746186146326758360385)
            ·
              refine ⟨3298309639609745068770289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4397746186146326758360385 3298309639609745068770289)
              ·
                refine ⟨2473732229707308801577717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3298309639609745068770289 2473732229707308801577717)
                ·
                  refine ⟨231912396535060200147911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2473732229707308801577717 231912396535060200147911)
                  ·
                    rfl

theorem cell22_2032415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 5].length) (baseStart_2032415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032415 prefixEnd_2032415 := by exact prefixLift 2032415
  have htrace : WordTrace (prefixWord ++ tailWord_2032415) baseStart_2032415 baseEnd_2032415 := by
    simpa [prefixWord, tailWord_2032415, baseEnd_2032415] using wordTrace_append hprefix tailTrace_2032415
  have hstable : (prefixWord ++ tailWord_2032415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032415).length < 2 ^ (prefixWord ++ tailWord_2032415).sum := by decide
  have hdescent : baseEnd_2032415 < baseStart_2032415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032428 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_2032428 : Nat := 118140960795 + 2032428 * 2 ^ 59
def prefixEnd_2032428 : Nat := 4983230072969 + 3 ^ 40 * 2032428 * 2
def baseEnd_2032428 : Nat := 695741639770852899868693

theorem tailTrace_2032428 : CollatzResearch.WordTrace tailWord_2032428 prefixEnd_2032428 695741639770852899868693 := by
  unfold tailWord_2032428
  simp only [CollatzResearch.WordTrace]
  refine ⟨37064369540433970956292969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49419159387245294608390625 37064369540433970956292969)
  ·
    refine ⟨27798277155325478217219727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37064369540433970956292969 27798277155325478217219727)
    ·
      refine ⟨41697415732988217325829591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27798277155325478217219727 41697415732988217325829591)
      ·
        refine ⟨62546123599482325988744387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41697415732988217325829591 62546123599482325988744387)
        ·
          refine ⟨93819185399223488983116581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62546123599482325988744387 93819185399223488983116581)
          ·
            refine ⟨17591097262354404184334359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93819185399223488983116581 17591097262354404184334359)
            ·
              refine ⟨26386645893531606276501539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17591097262354404184334359 26386645893531606276501539)
              ·
                refine ⟨39579968840297409414752309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26386645893531606276501539 39579968840297409414752309)
                ·
                  refine ⟨3710622078777882132633029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39579968840297409414752309 3710622078777882132633029)
                  ·
                    refine ⟨695741639770852899868693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3710622078777882132633029 695741639770852899868693)
                    ·
                      rfl

theorem cell22_2032428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_2032428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032428 prefixEnd_2032428 := by exact prefixLift 2032428
  have htrace : WordTrace (prefixWord ++ tailWord_2032428) baseStart_2032428 baseEnd_2032428 := by
    simpa [prefixWord, tailWord_2032428, baseEnd_2032428] using wordTrace_append hprefix tailTrace_2032428
  have hstable : (prefixWord ++ tailWord_2032428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032428).length < 2 ^ (prefixWord ++ tailWord_2032428).sum := by decide
  have hdescent : baseEnd_2032428 < baseStart_2032428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032430 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2032430 : Nat := 118140960795 + 2032430 * 2 ^ 59
def prefixEnd_2032430 : Nat := 4983230072969 + 3 ^ 40 * 2032430 * 2
def baseEnd_2032430 : Nat := 695742324411725561318687

theorem tailTrace_2032430 : CollatzResearch.WordTrace tailWord_2032430 prefixEnd_2032430 695742324411725561318687 := by
  unfold tailWord_2032430
  simp only [CollatzResearch.WordTrace]
  refine ⟨9266101503357587031769843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49419208017907130836105829 9266101503357587031769843)
  ·
    refine ⟨13899152255036380547654765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9266101503357587031769843 13899152255036380547654765)
    ·
      refine ⟨5212182095638642705370537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13899152255036380547654765 5212182095638642705370537)
      ·
        refine ⟨3909136571728982029027903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5212182095638642705370537 3909136571728982029027903)
        ·
          refine ⟨5863704857593473043541855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3909136571728982029027903 5863704857593473043541855)
          ·
            refine ⟨8795557286390209565312783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5863704857593473043541855 8795557286390209565312783)
            ·
              refine ⟨13193335929585314347969175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8795557286390209565312783 13193335929585314347969175)
              ·
                refine ⟨19790003894377971521953763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13193335929585314347969175 19790003894377971521953763)
                ·
                  refine ⟨29685005841566957282930645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19790003894377971521953763 29685005841566957282930645)
                  ·
                    refine ⟨695742324411725561318687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29685005841566957282930645 695742324411725561318687)
                    ·
                      rfl

theorem cell22_2032430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2032430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032430 prefixEnd_2032430 := by exact prefixLift 2032430
  have htrace : WordTrace (prefixWord ++ tailWord_2032430) baseStart_2032430 baseEnd_2032430 := by
    simpa [prefixWord, tailWord_2032430, baseEnd_2032430] using wordTrace_append hprefix tailTrace_2032430
  have hstable : (prefixWord ++ tailWord_2032430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032430).length < 2 ^ (prefixWord ++ tailWord_2032430).sum := by decide
  have hdescent : baseEnd_2032430 < baseStart_2032430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032458 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_2032458 : Nat := 118140960795 + 2032458 * 2 ^ 59
def prefixEnd_2032458 : Nat := 4983230072969 + 3 ^ 40 * 2032458 * 2
def baseEnd_2032458 : Nat := 695751909383942821618601

theorem tailTrace_2032458 : CollatzResearch.WordTrace tailWord_2032458 prefixEnd_2032458 695751909383942821618601 := by
  unfold tailWord_2032458
  simp only [CollatzResearch.WordTrace]
  refine ⟨18532458317689814259044507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49419888847172838024118685 18532458317689814259044507)
  ·
    refine ⟨27798687476534721388566761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18532458317689814259044507 27798687476534721388566761)
    ·
      refine ⟨20849015607401041041425071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27798687476534721388566761 20849015607401041041425071)
      ·
        refine ⟨31273523411101561562137607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20849015607401041041425071 31273523411101561562137607)
        ·
          refine ⟨46910285116652342343206411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31273523411101561562137607 46910285116652342343206411)
          ·
            refine ⟨70365427674978513514809617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46910285116652342343206411 70365427674978513514809617)
            ·
              refine ⟨52774070756233885136107213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70365427674978513514809617 52774070756233885136107213)
              ·
                refine ⟨19790276533587706926040205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52774070756233885136107213 19790276533587706926040205)
                ·
                  refine ⟨7421353700095390097265077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19790276533587706926040205 7421353700095390097265077)
                  ·
                    refine ⟨695751909383942821618601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7421353700095390097265077 695751909383942821618601)
                    ·
                      rfl

theorem cell22_2032458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_2032458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032458 prefixEnd_2032458 := by exact prefixLift 2032458
  have htrace : WordTrace (prefixWord ++ tailWord_2032458) baseStart_2032458 baseEnd_2032458 := by
    simpa [prefixWord, tailWord_2032458, baseEnd_2032458] using wordTrace_append hprefix tailTrace_2032458
  have hstable : (prefixWord ++ tailWord_2032458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032458).length < 2 ^ (prefixWord ++ tailWord_2032458).sum := by decide
  have hdescent : baseEnd_2032458 < baseStart_2032458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032505 : List Nat := [1, 2, 1, 3, 2, 3, 4, 6]
def baseStart_2032505 : Nat := 118140960795 + 2032505 * 2 ^ 59
def prefixEnd_2032505 : Nat := 4983230072969 + 3 ^ 40 * 2032505 * 2
def baseEnd_2032505 : Nat := 77307555382716707299273

theorem tailTrace_2032505 : CollatzResearch.WordTrace tailWord_2032505 prefixEnd_2032505 77307555382716707299273 := by
  unfold tailWord_2032505
  simp only [CollatzResearch.WordTrace]
  refine ⟨74131547501588984063138969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49421031667725989375425979 74131547501588984063138969)
  ·
    refine ⟨55598660626191738047354227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74131547501588984063138969 55598660626191738047354227)
    ·
      refine ⟨83397990939287607071031341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55598660626191738047354227 83397990939287607071031341)
      ·
        refine ⟨31274246602232852651636753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83397990939287607071031341 31274246602232852651636753)
        ·
          refine ⟨23455684951674639488727565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31274246602232852651636753 23455684951674639488727565)
          ·
            refine ⟨8795881856877989808272837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23455684951674639488727565 8795881856877989808272837)
            ·
              refine ⟨1649227848164623089051157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8795881856877989808272837 1649227848164623089051157)
              ·
                refine ⟨77307555382716707299273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1649227848164623089051157 77307555382716707299273)
                ·
                  rfl

theorem cell22_2032505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 6].length) (baseStart_2032505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032505 prefixEnd_2032505 := by exact prefixLift 2032505
  have htrace : WordTrace (prefixWord ++ tailWord_2032505) baseStart_2032505 baseEnd_2032505 := by
    simpa [prefixWord, tailWord_2032505, baseEnd_2032505] using wordTrace_append hprefix tailTrace_2032505
  have hstable : (prefixWord ++ tailWord_2032505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032505).length < 2 ^ (prefixWord ++ tailWord_2032505).sum := by decide
  have hdescent : baseEnd_2032505 < baseStart_2032505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032661 : List Nat := [1, 3, 2, 1, 4, 2, 3, 1, 2, 3]
def baseStart_2032661 : Nat := 118140960795 + 2032661 * 2 ^ 59
def prefixEnd_2032661 : Nat := 4983230072969 + 3 ^ 40 * 2032661 * 2
def baseEnd_2032661 : Nat := 695821400432517958792979

theorem tailTrace_2032661 : CollatzResearch.WordTrace tailWord_2032661 prefixEnd_2032661 695821400432517958792979 := by
  unfold tailWord_2032661
  simp only [CollatzResearch.WordTrace]
  refine ⟨74137237289023822705817837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49424824859349215137211891 74137237289023822705817837)
  ·
    refine ⟨27801463983383933514681689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74137237289023822705817837 27801463983383933514681689)
    ·
      refine ⟨20851097987537950136011267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27801463983383933514681689 20851097987537950136011267)
      ·
        refine ⟨31276646981306925204016901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20851097987537950136011267 31276646981306925204016901)
        ·
          refine ⟨5864371308995048475753169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31276646981306925204016901 5864371308995048475753169)
          ·
            refine ⟨4398278481746286356814877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5864371308995048475753169 4398278481746286356814877)
            ·
              refine ⟨1649354430654857383805579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4398278481746286356814877 1649354430654857383805579)
              ·
                refine ⟨2474031645982286075708369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649354430654857383805579 2474031645982286075708369)
                ·
                  refine ⟨1855523734486714556781277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2474031645982286075708369 1855523734486714556781277)
                  ·
                    refine ⟨695821400432517958792979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1855523734486714556781277 695821400432517958792979)
                    ·
                      rfl

theorem cell22_2032661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_2032661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032661 prefixEnd_2032661 := by exact prefixLift 2032661
  have htrace : WordTrace (prefixWord ++ tailWord_2032661) baseStart_2032661 baseEnd_2032661 := by
    simpa [prefixWord, tailWord_2032661, baseEnd_2032661] using wordTrace_append hprefix tailTrace_2032661
  have hstable : (prefixWord ++ tailWord_2032661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032661).length < 2 ^ (prefixWord ++ tailWord_2032661).sum := by decide
  have hdescent : baseEnd_2032661 < baseStart_2032661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032674 : List Nat := [3, 3, 1, 1, 1, 5, 2, 6]
def baseStart_2032674 : Nat := 118140960795 + 2032674 * 2 ^ 59
def prefixEnd_2032674 : Nat := 4983230072969 + 3 ^ 40 * 2032674 * 2
def baseEnd_2032674 : Nat := 77313983399798917579771

theorem tailTrace_2032674 : CollatzResearch.WordTrace tailWord_2032674 prefixEnd_2032674 77313983399798917579771 := by
  unfold tailWord_2032674
  simp only [CollatzResearch.WordTrace]
  refine ⟨18534427859494181481510269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49425140958651150617360717 18534427859494181481510269)
  ·
    refine ⟨6950410447310318055566351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18534427859494181481510269 6950410447310318055566351)
    ·
      refine ⟨10425615670965477083349527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6950410447310318055566351 10425615670965477083349527)
      ·
        refine ⟨15638423506448215625024291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10425615670965477083349527 15638423506448215625024291)
        ·
          refine ⟨23457635259672323437536437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15638423506448215625024291 23457635259672323437536437)
          ·
            refine ⟨2199153305594280322269041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23457635259672323437536437 2199153305594280322269041)
            ·
              refine ⟨1649364979195710241701781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2199153305594280322269041 1649364979195710241701781)
              ·
                refine ⟨77313983399798917579771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1649364979195710241701781 77313983399798917579771)
                ·
                  rfl

theorem cell22_2032674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 6].length) (baseStart_2032674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032674 prefixEnd_2032674 := by exact prefixLift 2032674
  have htrace : WordTrace (prefixWord ++ tailWord_2032674) baseStart_2032674 baseEnd_2032674 := by
    simpa [prefixWord, tailWord_2032674, baseEnd_2032674] using wordTrace_append hprefix tailTrace_2032674
  have hstable : (prefixWord ++ tailWord_2032674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032674).length < 2 ^ (prefixWord ++ tailWord_2032674).sum := by decide
  have hdescent : baseEnd_2032674 < baseStart_2032674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032757 : List Nat := [1, 3, 4, 3, 1, 2, 2, 2, 1, 3]
def baseStart_2032757 : Nat := 118140960795 + 2032757 * 2 ^ 59
def prefixEnd_2032757 : Nat := 4983230072969 + 3 ^ 40 * 2032757 * 2
def baseEnd_2032757 : Nat := 695854263194405708392685

theorem tailTrace_2032757 : CollatzResearch.WordTrace tailWord_2032757 prefixEnd_2032757 695854263194405708392685 := by
  unfold tailWord_2032757
  simp only [CollatzResearch.WordTrace]
  refine ⟨74140738696676031101312525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49427159131117354067541683 74140738696676031101312525)
  ·
    refine ⟨27802777011253511662992197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74140738696676031101312525 27802777011253511662992197)
    ·
      refine ⟨5213020689610033436811037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27802777011253511662992197 5213020689610033436811037)
      ·
        refine ⟨1954882758603762538804139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5213020689610033436811037 1954882758603762538804139)
        ·
          refine ⟨2932324137905643808206209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1954882758603762538804139 2932324137905643808206209)
          ·
            refine ⟨2199243103429232856154657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2932324137905643808206209 2199243103429232856154657)
            ·
              refine ⟨1649432327571924642115993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2199243103429232856154657 1649432327571924642115993)
              ·
                refine ⟨1237074245678943481586995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1649432327571924642115993 1237074245678943481586995)
                ·
                  refine ⟨1855611368518415222380493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237074245678943481586995 1855611368518415222380493)
                  ·
                    refine ⟨695854263194405708392685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1855611368518415222380493 695854263194405708392685)
                    ·
                      rfl

theorem cell22_2032757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_2032757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032757 prefixEnd_2032757 := by exact prefixLift 2032757
  have htrace : WordTrace (prefixWord ++ tailWord_2032757) baseStart_2032757 baseEnd_2032757 := by
    simpa [prefixWord, tailWord_2032757, baseEnd_2032757] using wordTrace_append hprefix tailTrace_2032757
  have hstable : (prefixWord ++ tailWord_2032757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032757).length < 2 ^ (prefixWord ++ tailWord_2032757).sum := by decide
  have hdescent : baseEnd_2032757 < baseStart_2032757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032764 : List Nat := [2, 2, 2, 1, 1, 3, 3, 4, 4]
def baseStart_2032764 : Nat := 118140960795 + 2032764 * 2 ^ 59
def prefixEnd_2032764 : Nat := 4983230072969 + 3 ^ 40 * 2032764 * 2
def baseEnd_2032764 : Nat := 231952219812486674489221

theorem tailTrace_2032764 : CollatzResearch.WordTrace tailWord_2032764 prefixEnd_2032764 231952219812486674489221 := by
  unfold tailWord_2032764
  simp only [CollatzResearch.WordTrace]
  refine ⟨37070497003825335648408673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49427329338433780864544897 37070497003825335648408673)
  ·
    refine ⟨27802872752869001736306505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37070497003825335648408673 27802872752869001736306505)
    ·
      refine ⟨20852154564651751302229879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27802872752869001736306505 20852154564651751302229879)
      ·
        refine ⟨31278231846977626953344819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20852154564651751302229879 31278231846977626953344819)
        ·
          refine ⟨46917347770466440430017229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31278231846977626953344819 46917347770466440430017229)
          ·
            refine ⟨17594005413924915161256461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46917347770466440430017229 17594005413924915161256461)
            ·
              refine ⟨6597752030221843185471173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17594005413924915161256461 6597752030221843185471173)
              ·
                refine ⟨1237078505666595597275845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6597752030221843185471173 1237078505666595597275845)
                ·
                  refine ⟨231952219812486674489221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1237078505666595597275845 231952219812486674489221)
                  ·
                    rfl

theorem cell22_2032764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_2032764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032764 prefixEnd_2032764 := by exact prefixLift 2032764
  have htrace : WordTrace (prefixWord ++ tailWord_2032764) baseStart_2032764 baseEnd_2032764 := by
    simpa [prefixWord, tailWord_2032764, baseEnd_2032764] using wordTrace_append hprefix tailTrace_2032764
  have hstable : (prefixWord ++ tailWord_2032764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032764).length < 2 ^ (prefixWord ++ tailWord_2032764).sum := by decide
  have hdescent : baseEnd_2032764 < baseStart_2032764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032794 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_2032794 : Nat := 118140960795 + 2032794 * 2 ^ 59
def prefixEnd_2032794 : Nat := 4983230072969 + 3 ^ 40 * 2032794 * 2
def baseEnd_2032794 : Nat := 695866929050549945217571

theorem tailTrace_2032794 : CollatzResearch.WordTrace tailWord_2032794 prefixEnd_2032794 695866929050549945217571 := by
  unfold tailWord_2032794
  simp only [CollatzResearch.WordTrace]
  refine ⟨18535522049385496605102359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49428058798361324280272957 18535522049385496605102359)
  ·
    refine ⟨27803283074078244907653539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18535522049385496605102359 27803283074078244907653539)
    ·
      refine ⟨41704924611117367361480309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27803283074078244907653539 41704924611117367361480309)
      ·
        refine ⟨3909836682292253190138779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41704924611117367361480309 3909836682292253190138779)
        ·
          refine ⟨5864755023438379785208169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3909836682292253190138779 5864755023438379785208169)
          ·
            refine ⟨4398566267578784838906127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5864755023438379785208169 4398566267578784838906127)
            ·
              refine ⟨6597849401368177258359191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4398566267578784838906127 6597849401368177258359191)
              ·
                refine ⟨9896774102052265887538787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6597849401368177258359191 9896774102052265887538787)
                ·
                  refine ⟨14845161153078398831308181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9896774102052265887538787 14845161153078398831308181)
                  ·
                    refine ⟨695866929050549945217571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14845161153078398831308181 695866929050549945217571)
                    ·
                      rfl

theorem cell22_2032794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_2032794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032794 prefixEnd_2032794 := by exact prefixLift 2032794
  have htrace : WordTrace (prefixWord ++ tailWord_2032794) baseStart_2032794 baseEnd_2032794 := by
    simpa [prefixWord, tailWord_2032794, baseEnd_2032794] using wordTrace_append hprefix tailTrace_2032794
  have hstable : (prefixWord ++ tailWord_2032794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032794).length < 2 ^ (prefixWord ++ tailWord_2032794).sum := by decide
  have hdescent : baseEnd_2032794 < baseStart_2032794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032798 : List Nat := [4, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_2032798 : Nat := 118140960795 + 2032798 * 2 ^ 59
def prefixEnd_2032798 : Nat := 4983230072969 + 3 ^ 40 * 2032798 * 2
def baseEnd_2032798 : Nat := 231956099444098422705853

theorem tailTrace_2032798 : CollatzResearch.WordTrace tailWord_2032798 prefixEnd_2032798 231956099444098422705853 := by
  unfold tailWord_2032798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9267779261190936887944381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49428156059684996735703365 9267779261190936887944381)
  ·
    refine ⟨3475417222946601332979143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9267779261190936887944381 3475417222946601332979143)
    ·
      refine ⟨5213125834419901999468715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3475417222946601332979143 5213125834419901999468715)
      ·
        refine ⟨7819688751629852999203073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5213125834419901999468715 7819688751629852999203073)
        ·
          refine ⟨5864766563722389749402305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7819688751629852999203073 5864766563722389749402305)
          ·
            refine ⟨4398574922791792312051729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5864766563722389749402305 4398574922791792312051729)
            ·
              refine ⟨3298931192093844234038797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4398574922791792312051729 3298931192093844234038797)
              ·
                refine ⟨1237099197035191587764549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3298931192093844234038797 1237099197035191587764549)
                ·
                  refine ⟨231956099444098422705853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1237099197035191587764549 231956099444098422705853)
                  ·
                    rfl

theorem cell22_2032798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_2032798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032798 prefixEnd_2032798 := by exact prefixLift 2032798
  have htrace : WordTrace (prefixWord ++ tailWord_2032798) baseStart_2032798 baseEnd_2032798 := by
    simpa [prefixWord, tailWord_2032798, baseEnd_2032798] using wordTrace_append hprefix tailTrace_2032798
  have hstable : (prefixWord ++ tailWord_2032798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032798).length < 2 ^ (prefixWord ++ tailWord_2032798).sum := by decide
  have hdescent : baseEnd_2032798 < baseStart_2032798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032912 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 7, 6]
def baseStart_2032912 : Nat := 118140960795 + 2032912 * 2 ^ 59
def prefixEnd_2032912 : Nat := 4983230072969 + 3 ^ 40 * 2032912 * 2
def baseEnd_2032912 : Nat := 695907322862036970767209

theorem tailTrace_2032912 : CollatzResearch.WordTrace tailWord_2032912 prefixEnd_2032912 695907322862036970767209 := by
  unfold tailWord_2032912
  simp only [CollatzResearch.WordTrace]
  refine ⟨37073196005557246286602495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49430928007409661715469993 37073196005557246286602495)
  ·
    refine ⟨55609794008335869429903743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37073196005557246286602495 55609794008335869429903743)
    ·
      refine ⟨83414691012503804144855615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55609794008335869429903743 83414691012503804144855615)
      ·
        refine ⟨125122036518755706217283423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83414691012503804144855615 125122036518755706217283423)
        ·
          refine ⟨187683054778133559325925135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125122036518755706217283423 187683054778133559325925135)
          ·
            refine ⟨281524582167200338988887703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187683054778133559325925135 281524582167200338988887703)
            ·
              refine ⟨422286873250800508483331555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281524582167200338988887703 422286873250800508483331555)
              ·
                refine ⟨633430309876200762724997333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422286873250800508483331555 633430309876200762724997333)
                ·
                  refine ⟨14846022887723455376367125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 633430309876200762724997333 14846022887723455376367125)
                  ·
                    refine ⟨695907322862036970767209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14846022887723455376367125 695907322862036970767209)
                    ·
                      rfl

theorem cell22_2032912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_2032912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032912 prefixEnd_2032912 := by exact prefixLift 2032912
  have htrace : WordTrace (prefixWord ++ tailWord_2032912) baseStart_2032912 baseEnd_2032912 := by
    simpa [prefixWord, tailWord_2032912, baseEnd_2032912] using wordTrace_append hprefix tailTrace_2032912
  have hstable : (prefixWord ++ tailWord_2032912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032912).length < 2 ^ (prefixWord ++ tailWord_2032912).sum := by decide
  have hdescent : baseEnd_2032912 < baseStart_2032912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032926 : List Nat := [4, 3, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_2032926 : Nat := 118140960795 + 2032926 * 2 ^ 59
def prefixEnd_2032926 : Nat := 4983230072969 + 3 ^ 40 * 2032926 * 2
def baseEnd_2032926 : Nat := 695912115348145600917167

theorem tailTrace_2032926 : CollatzResearch.WordTrace tailWord_2032926 prefixEnd_2032926 695912115348145600917167 := by
  unfold tailWord_2032926
  simp only [CollatzResearch.WordTrace]
  refine ⟨9268362829132971620526829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49431268422042515309476421 9268362829132971620526829)
  ·
    refine ⟨3475636060924864357697561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9268362829132971620526829 3475636060924864357697561)
    ·
      refine ⟨2606727045693648268273171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3475636060924864357697561 2606727045693648268273171)
      ·
        refine ⟨3910090568540472402409757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2606727045693648268273171 3910090568540472402409757)
        ·
          refine ⟨1466283963202677150903659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3910090568540472402409757 1466283963202677150903659)
          ·
            refine ⟨2199425944804015726355489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466283963202677150903659 2199425944804015726355489)
            ·
              refine ⟨1649569458603011794766617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2199425944804015726355489 1649569458603011794766617)
              ·
                refine ⟨1237177093952258846074963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1649569458603011794766617 1237177093952258846074963)
                ·
                  refine ⟨1855765640928388269112445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237177093952258846074963 1855765640928388269112445)
                  ·
                    refine ⟨695912115348145600917167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1855765640928388269112445 695912115348145600917167)
                    ·
                      rfl

theorem cell22_2032926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_2032926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032926 prefixEnd_2032926 := by exact prefixLift 2032926
  have htrace : WordTrace (prefixWord ++ tailWord_2032926) baseStart_2032926 baseEnd_2032926 := by
    simpa [prefixWord, tailWord_2032926, baseEnd_2032926] using wordTrace_append hprefix tailTrace_2032926
  have hstable : (prefixWord ++ tailWord_2032926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032926).length < 2 ^ (prefixWord ++ tailWord_2032926).sum := by decide
  have hdescent : baseEnd_2032926 < baseStart_2032926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032927 : List Nat := [1, 1, 2, 4, 14]
def baseStart_2032927 : Nat := 118140960795 + 2032927 * 2 ^ 59
def prefixEnd_2032927 : Nat := 4983230072969 + 3 ^ 40 * 2032927 * 2
def baseEnd_2032927 : Nat := 2863837274356304245441

theorem tailTrace_2032927 : CollatzResearch.WordTrace tailWord_2032927 prefixEnd_2032927 2863837274356304245441 := by
  unfold tailWord_2032927
  simp only [CollatzResearch.WordTrace]
  refine ⟨74146939106060150135001035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49431292737373433423334023 74146939106060150135001035)
  ·
    refine ⟨111220408659090225202501553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74146939106060150135001035 111220408659090225202501553)
    ·
      refine ⟨83415306494317668901876165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111220408659090225202501553 83415306494317668901876165)
      ·
        refine ⟨15640369967684562919101781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83415306494317668901876165 15640369967684562919101781)
        ·
          refine ⟨2863837274356304245441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 15640369967684562919101781 2863837274356304245441)
          ·
            rfl

theorem cell22_2032927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 14].length) (baseStart_2032927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032927 prefixEnd_2032927 := by exact prefixLift 2032927
  have htrace : WordTrace (prefixWord ++ tailWord_2032927) baseStart_2032927 baseEnd_2032927 := by
    simpa [prefixWord, tailWord_2032927, baseEnd_2032927] using wordTrace_append hprefix tailTrace_2032927
  have hstable : (prefixWord ++ tailWord_2032927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032927).length < 2 ^ (prefixWord ++ tailWord_2032927).sum := by decide
  have hdescent : baseEnd_2032927 < baseStart_2032927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032931 : List Nat := [1, 1, 1, 4, 2, 3, 1, 4, 2, 3]
def baseStart_2032931 : Nat := 118140960795 + 2032931 * 2 ^ 59
def prefixEnd_2032931 : Nat := 4983230072969 + 3 ^ 40 * 2032931 * 2
def baseEnd_2032931 : Nat := 695913826950327254542151

theorem tailTrace_2032931 : CollatzResearch.WordTrace tailWord_2032931 prefixEnd_2032931 695913826950327254542151 := by
  unfold tailWord_2032931
  simp only [CollatzResearch.WordTrace]
  refine ⟨74147084998045658818146647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49431389998697105878764431 74147084998045658818146647)
  ·
    refine ⟨111220627497068488227219971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74147084998045658818146647 111220627497068488227219971)
    ·
      refine ⟨166830941245602732340829957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111220627497068488227219971 166830941245602732340829957)
      ·
        refine ⟨31280801483550512313905617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166830941245602732340829957 31280801483550512313905617)
        ·
          refine ⟨23460601112662884235429213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31280801483550512313905617 23460601112662884235429213)
          ·
            refine ⟨8797725417248581588285955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23460601112662884235429213 8797725417248581588285955)
            ·
              refine ⟨13196588125872872382428933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8797725417248581588285955 13196588125872872382428933)
              ·
                refine ⟨2474360273601163571705425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13196588125872872382428933 2474360273601163571705425)
                ·
                  refine ⟨1855770205200872678779069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2474360273601163571705425 1855770205200872678779069)
                  ·
                    refine ⟨695913826950327254542151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1855770205200872678779069 695913826950327254542151)
                    ·
                      rfl

theorem cell22_2032931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 3].length) (baseStart_2032931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032931 prefixEnd_2032931 := by exact prefixLift 2032931
  have htrace : WordTrace (prefixWord ++ tailWord_2032931) baseStart_2032931 baseEnd_2032931 := by
    simpa [prefixWord, tailWord_2032931, baseEnd_2032931] using wordTrace_append hprefix tailTrace_2032931
  have hstable : (prefixWord ++ tailWord_2032931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032931).length < 2 ^ (prefixWord ++ tailWord_2032931).sum := by decide
  have hdescent : baseEnd_2032931 < baseStart_2032931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032933 : List Nat := [1, 3, 1, 2, 4, 1, 4, 2, 4]
def baseStart_2032933 : Nat := 118140960795 + 2032933 * 2 ^ 59
def prefixEnd_2032933 : Nat := 4983230072969 + 3 ^ 40 * 2032933 * 2
def baseEnd_2032933 : Nat := 231971503863733305330715

theorem tailTrace_2032933 : CollatzResearch.WordTrace tailWord_2032933 prefixEnd_2032933 231971503863733305330715 := by
  unfold tailWord_2032933
  simp only [CollatzResearch.WordTrace]
  refine ⟨74147157944038413159719453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49431438629358942106479635 74147157944038413159719453)
  ·
    refine ⟨27805184229014404934894795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74147157944038413159719453 27805184229014404934894795)
    ·
      refine ⟨41707776343521607402342193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27805184229014404934894795 41707776343521607402342193)
      ·
        refine ⟨31280832257641205551756645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41707776343521607402342193 31280832257641205551756645)
        ·
          refine ⟨5865156048307726040954371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31280832257641205551756645 5865156048307726040954371)
          ·
            refine ⟨8797734072461589061431557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5865156048307726040954371 8797734072461589061431557)
            ·
              refine ⟨1649575138586547949018417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8797734072461589061431557 1649575138586547949018417)
              ·
                refine ⟨1237181353939910961763813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1649575138586547949018417 1237181353939910961763813)
                ·
                  refine ⟨231971503863733305330715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1237181353939910961763813 231971503863733305330715)
                  ·
                    rfl

theorem cell22_2032933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_2032933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032933 prefixEnd_2032933 := by exact prefixLift 2032933
  have htrace : WordTrace (prefixWord ++ tailWord_2032933) baseStart_2032933 baseEnd_2032933 := by
    simpa [prefixWord, tailWord_2032933, baseEnd_2032933] using wordTrace_append hprefix tailTrace_2032933
  have hstable : (prefixWord ++ tailWord_2032933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032933).length < 2 ^ (prefixWord ++ tailWord_2032933).sum := by decide
  have hdescent : baseEnd_2032933 < baseStart_2032933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032948 : List Nat := [2, 5, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2032948 : Nat := 118140960795 + 2032948 * 2 ^ 59
def prefixEnd_2032948 : Nat := 4983230072969 + 3 ^ 40 * 2032948 * 2
def baseEnd_2032948 : Nat := 695919646397744876867099

theorem tailTrace_2032948 : CollatzResearch.WordTrace tailWord_2032948 prefixEnd_2032948 695919646397744876867099 := by
  unfold tailWord_2032948
  simp only [CollatzResearch.WordTrace]
  refine ⟨37073852519492035360757749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49431803359322713814343665 37073852519492035360757749)
  ·
    refine ⟨3475673673702378315071039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37073852519492035360757749 3475673673702378315071039)
    ·
      refine ⟨5213510510553567472606559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3475673673702378315071039 5213510510553567472606559)
      ·
        refine ⟨7820265765830351208909839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5213510510553567472606559 7820265765830351208909839)
        ·
          refine ⟨11730398648745526813364759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7820265765830351208909839 11730398648745526813364759)
          ·
            refine ⟨17595597973118290220047139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11730398648745526813364759 17595597973118290220047139)
            ·
              refine ⟨26393396959677435330070709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17595597973118290220047139 26393396959677435330070709)
              ·
                refine ⟨2474380964969759562194129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26393396959677435330070709 2474380964969759562194129)
                ·
                  refine ⟨1855785723727319671645597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2474380964969759562194129 1855785723727319671645597)
                  ·
                    refine ⟨695919646397744876867099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1855785723727319671645597 695919646397744876867099)
                    ·
                      rfl

theorem cell22_2032948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2032948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2032948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2032948 prefixEnd_2032948 := by exact prefixLift 2032948
  have htrace : WordTrace (prefixWord ++ tailWord_2032948) baseStart_2032948 baseEnd_2032948 := by
    simpa [prefixWord, tailWord_2032948, baseEnd_2032948] using wordTrace_append hprefix tailTrace_2032948
  have hstable : (prefixWord ++ tailWord_2032948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032948).length < 2 ^ (prefixWord ++ tailWord_2032948).sum := by decide
  have hdescent : baseEnd_2032948 < baseStart_2032948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033036 : List Nat := [2, 2, 1, 2, 1, 3, 1, 5, 1, 4]
def baseStart_2033036 : Nat := 118140960795 + 2033036 * 2 ^ 59
def prefixEnd_2033036 : Nat := 4983230072969 + 3 ^ 40 * 2033036 * 2
def baseEnd_2033036 : Nat := 695949770596141980666829

theorem tailTrace_2033036 : CollatzResearch.WordTrace tailWord_2033036 prefixEnd_2033036 695949770596141980666829 := by
  unfold tailWord_2033036
  simp only [CollatzResearch.WordTrace]
  refine ⟨37075457331332630875359481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49433943108443507833812641 37075457331332630875359481)
  ·
    refine ⟨27806592998499473156519611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37075457331332630875359481 27806592998499473156519611)
    ·
      refine ⟨41709889497749209734779417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27806592998499473156519611 41709889497749209734779417)
      ·
        refine ⟨31282417123311907301084563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41709889497749209734779417 31282417123311907301084563)
        ·
          refine ⟨46923625684967860951626845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31282417123311907301084563 46923625684967860951626845)
          ·
            refine ⟨17596359631862947856860067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46923625684967860951626845 17596359631862947856860067)
            ·
              refine ⟨26394539447794421785290101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17596359631862947856860067 26394539447794421785290101)
              ·
                refine ⟨2474488073230727042370947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26394539447794421785290101 2474488073230727042370947)
                ·
                  refine ⟨3711732109846090563556421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474488073230727042370947 3711732109846090563556421)
                  ·
                    refine ⟨695949770596141980666829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3711732109846090563556421 695949770596141980666829)
                    ·
                      rfl

theorem cell22_2033036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_2033036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033036 prefixEnd_2033036 := by exact prefixLift 2033036
  have htrace : WordTrace (prefixWord ++ tailWord_2033036) baseStart_2033036 baseEnd_2033036 := by
    simpa [prefixWord, tailWord_2033036, baseEnd_2033036] using wordTrace_append hprefix tailTrace_2033036
  have hstable : (prefixWord ++ tailWord_2033036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033036).length < 2 ^ (prefixWord ++ tailWord_2033036).sum := by decide
  have hdescent : baseEnd_2033036 < baseStart_2033036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
